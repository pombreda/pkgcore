# Copyright: 2004-2012 Brian Harring <ferringb@gmail.com> (BSD/GPL2)
# License: GPL2


"""
subprocess related functionality
"""

__all__ = [
    "spawn", "spawn_sandbox", "spawn_bash", "spawn_fakeroot",
    "spawn_get_output", "find_binary"]

import errno
import fcntl
import itertools
import os
import signal
import sys
from threading import Thread

from pkgcore.const import (
    BASH_BINARY, SANDBOX_BINARY, FAKED_PATH, LIBFAKEROOT_PATH)

from snakeoil.currying import partial
from snakeoil import klass
from snakeoil.osutils import listdir, access
from snakeoil.mappings import ProtectedDict, ImmutableDict
from snakeoil.process import get_proc_count, find_binary, CommandNotFound, closerange
from snakeoil import weakrefs

# Custom import of subprocess so we can remove subprocess.Popen's __del__
# this results in our code using our version of Popen (which is annoying, but fine).


class _del_object(object):
    __metaclass__ = weakrefs.WeakRefFinalizer
    __finalizer__ = lambda self:None


original = sys.modules.pop('subprocess', None)
original_object = object
__builtins__['object'] = _del_object
_subprocess = __import__('subprocess', globals())
__builtins__['object'] = original_object
if original is not None:
    sys.modules['subprocess'] = original
    # Ensure constants are the same between the two; while these constants
    # are currently integers, we do the assign to protect against them
    # becoming objects down the line.
    for clone in ("PIPE", "STDOUT"):
        setattr(_subprocess, clone, getattr(original, clone))
    del clone

del original

# Left for compatibility.
max_fd_limit = _subprocess.MAXFD


class PIPE_W(object):

    __metaclass__ = weakrefs.WeakRefFinalizer
    is_write = True

    def __init__(self, name, buffering=0):
        self.name = name
        self.buffering = buffering
        self.child_fd = self.parent_fd = None

    def _create(self):
        if self.child_fd is None:
            fds = os.pipe()
            if self.is_write:
                fds = reversed(fds)
            self.parent_fd, self.child_fd = fds
        # Bring the handle into existance to simplify __del__ scenarios.
        self.handle

    def _parent_cleanup(self):
        if self.child_fd is not None:
            try:
                os.close(self.child_fd)
                self.child_fd = None
            except EnvironmentError, e:
                pass

    def __del__(self):
        try:
            self._parent_cleanup()
        except EnvironmentError:
            pass
        if not hasattr(self, '_handle') and self.parent_fd is not None:
            # Only close this if we've not given out a handle;
            # if we have, let the handle's auto closing during GC sort it.
            try:
                os.close(self.parent_fd)
            except EnvironmentError, e:
                pass

    @klass.jit_attr
    def handle(self):
        mode = 'w'
        if not self.is_write:
            mode = 'r'
        return os.fdopen(self.parent_fd, mode, self.buffering)

    def alias(self, new_name):
        obj = self.__class__(self, new_name, buffering=self.buffering)
        obj.parent_fd, obj.child_fd = self.parent_fd, self.child_fd
        obj._handle = self._handle

    def __repr__(self):
        return "%s(%r, %s)" % (self.__class__.__name__, self.name,
                               self.buffering)
    __str__ = __repr__


class PIPE_R(PIPE_W):

    is_write = False


class _LazyDup(object):
    def __init__(self, value):
        if not value.startswith('@'):
            raise ValueError("Lazy duplication must start with @: %s" % value)
        try:
            self.fd = int(value)
        except ValueError:
            raise ValueError("Lazy duplication targets must be an integer: %s"
                             % value)

class process(_subprocess.Popen):

    def __init__(self, command, **kwds):
        """wrapper around execve

        :type mycommand: list or string
        :type env: mapping with string keys and values
        :param name: controls what the process is named
            (what it would show up as under top for example)
        :type fd_pipes: mapping from existing fd to fd (inside the new process)
        :param fd_pipes: controls what fd's are left open in the spawned process-
        """
        # mycommand is either a str or a list
        if isinstance(command, str):
            command = command.split()
        fd_pipes = kwds.pop("fd_pipes", None)
        if fd_pipes is None:
            fd_pipes = {0:0, 1:1, 2:2}
        elif not hasattr(fd_pipes, 'keys'):
            fd_pipes = dict((idx, val) for (idx, val) in
                            enumerate(fd_pipes) if val != -1)
        for key, value in fd_pipes.iteritems():
            if isinstance(value, basestring):
                fd_pipes[key] = _LazyDup(value)

        self.fd_pipes = fd_pipes
        kwds.setdefault('env', {})
        for x in "uid gid groups umask".split():
            setattr(self, x, kwds.pop(x, None))
        # We manually close fds ourselves, but we still need
        # subprocess to invoke this pathway so we can find out what the
        # errpipe's fd is.
        kwds['close_fds'] = True
        self._secondary_preexec = kwds.pop('preexec_fn', None)
        kwds['preexec_fn'] = self._forced_preexec_fn
        self._errpipe_fd = None
        self._read_pipes, self._write_pipes = None, None
        self._buffered_write_handles = None
        name = kwds.pop('name', None)
        if name is not None:
            kwds.setdefault('executable', command[0])
            command = [name] + command[1:]
        _subprocess.Popen.__init__(self, command, **kwds)

    def _execute_child(self, *args, **kwds):
        curpid = os.getpid()
        self._prefork_pipe_setup()
        try:
            return _subprocess.Popen._execute_child(self, *args, **kwds)
        finally:
            if curpid != os.getpid():
                # Subprocess can be stupid and crash its way through the
                # child's stack if it fails early.  Preclude that from
                # happening.
                os._exit(1)

            self._postfork_pipe_setup()

    @staticmethod
    def _os_write_override(functor, fd_map, passed_fd, *args, **kwds):
        """Hack for overriding os.write in the child.

        This is done due to the fact subprocess assumes it has full rein
        over the childs fd space, including being able to leave fd's where it
        wants.  This makes it russian roulet to ensure fds are in place for
        the invoked child, as such we note the errpipe fd, and redirect
        the invocation to the correct fd on the fly."""
        return functor(fd_map.get(passed_fd, passed_fd), *args, **kwds)

    def _close_fds(self, but):
        # Delay closing; we address it in full w/in _forced_prexec_fn.
        # Just record the fd so we know what it is.
        self._errpipe_fd = but

    def _set_cloexec_flag(self, fd, enabled=True):
        # This is the py2.7 signature; we force this since
        # <2.7 doesn't have the enabled option which we want (in the process
        # making it slightly more efficient via doing the F_SETFD only if
        # needed).
        cloexec = getattr(fcntl, 'FD_CLOEXEC', None)

        if cloexec is None:
            return

        orig_flags = new_flags = fcntl.fcntl(fd, fcntl.F_GETFD)

        if enabled:
            new_flags |= cloexec
        else:
            new_flags &= ~cloexec

        if new_flags != orig_flags:
            fcntl.fcntl(fd, fcntl.F_SETFD, new_flags)

    def _prefork_pipe_setup(self):
        # Automatically swap in stdin/stdout/stderr to ensure they
        # get flushed if passed in via fd.
        replace = dict((x.fileno(), x) for x in
                       (sys.stdin, sys.stdout, sys.stderr))
        buffered, writes, reads = [], [], []
        for src_fd in self.fd_pipes.itervalues():
            src_fd = replace.get(src_fd, src_fd)
            if hasattr(src_fd, 'fileno'):
                # Flush any existing output prior to letting
                # an uncontrolled process get at it.
                src_fd.flush()
                src_fd = src_fd.fileno()
            elif isinstance(src_fd, PIPE_W):
                src_fd._create()
                setattr(self, src_fd.name, src_fd.handle)

                if src_fd.is_write:
                    writes.append(src_fd)
                    if src_fd.buffering != 0:
                        buffered.append(src_fd)
                else:
                    reads.append(src_fd)

        self._read_pipes = ImmutableDict((x.name, x.handle) for x in reads)
        self._write_pipes = ImmutableDict((x.name, x.handle) for x in writes)
        self._buffered_write_handles = frozenset(x.handle for x in buffered)

    def _postfork_pipe_setup(self):
        for handle in self.fd_pipes.itervalues():
            if isinstance(handle, PIPE_W):
                handle._parent_cleanup()

    def _preexec_pipe_setup(self, fd_pipes):
        null = None
        for trg_fd, src_fd in fd_pipes.iteritems():
            if src_fd is None:
                # Swap in /dev/null...
                if null is None:
                    null = os.open('/dev/null', os.O_RDWR)
                fd_pipes[trg_fd] = null
            elif isinstance(src_fd, PIPE_W):
                fd_pipes[trg_fd] = src_fd.child_fd
            else:
                assert isinstance(src_fd, (_LazyDup, int, long))

    def _preexec_setup_fds(self):

        # Work from a copy so we don't lose any references to
        # pipe objects.
        fd_pipes = self.fd_pipes.copy()
        self._preexec_pipe_setup(fd_pipes)

        def _find_unused_pid(protected):
            for potential in itertools.count():
                if potential not in protected:
                    protected.add(potential)
                    yield potential

        my_fds = {}

        # To protect from cases where direct assignment could
        # clobber needed fds ({1:2, 2:1}) we first dupe the fds
        # into unused fds.
        targets = set(fd_pipes)
        targets.add(self._errpipe_fd)
        protected = set(targets)
        sources = set(fd_pipes.itervalues())
        sources.add(self._errpipe_fd)
        protected.update(sources)

        fd_source = _find_unused_pid(protected)

        # It's possible that subprocess's errpipe (for failed exec) is in
        # the way of an fd we want to assign; if so, move it, and monkeypatch
        # os.write to rewrite on the fly (_execute_child will still think the
        # fd is at 6, when we've moved it to 9 for example).  Yes this is evil,
        # but that's the python stdlib for you...

        if self._errpipe_fd in fd_pipes:
            # Reassignment required.
            new_fd = fd_source.next()
            targets.add(new_fd)
            sources.add(new_fd)
            os.dup2(self._errpipe_fd, new_fd)
            protected.discard(self._errpipe_fd)
            targets.discard(self._errpipe_fd)
            sources.discard(self._errpipe_fd)
            self._set_cloexec_flag(new_fd)
            # Monkey patch...
            os.write = partial(self._os_write_override, os.write,
                               {self._errpipe_fd:new_fd})
            os.close = partial(self._os_write_override, os.close,
                               {self._errpipe_fd:new_fd})

        lazy_dupes = []

        for trg_fd, src_fd in fd_pipes.iteritems():
            if isinstance(src_fd, _LazyDup):
                lazy_dupes.append((trg_fd, src_fd))
            if trg_fd == src_fd:
                # Strip cloexec so the child actually gets the fd.
                self._set_cloexec_flag(trg_fd, False)
            else:
                # No need to worry about cloexec here since dup strips it.
                if trg_fd not in sources:
                    # Nothing is in the way; move it immediately.
                    # Via the code above, we know it won't be stomped either.
                    os.dup2(src_fd, trg_fd)
                else:
                    x = my_fds[trg_fd] = fd_source.next()
                    os.dup2(src_fd, x)

        # reassign whats required now.
        for trg_fd, src_fd in my_fds.iteritems():
            os.dup2(src_fd, trg_fd)

        # Finalize lazy duplication.
        for trg_fd, lazy_src in lazy_dupes:
            os.dup2(lazy_src.fd, trg_fd)

        # Then close _all_ fds that haven't been explictly
        # requested to be kept open.
        last = 0
        for fd in sorted(targets):
            if fd != last:
                closerange(last, fd)
            last = fd + 1

        closerange(last, _subprocess.MAXFD)

    def _forced_preexec_fn(self):
        self._preexec_setup_fds()
        # Set requested process permissions.
        if self.gid:
            os.setgid(self.gid)
        if self.groups:
            os.setgroups(self.groups)
        if self.uid:
            os.setuid(self.uid)
        if self.umask:
            os.umask(self.umask)

        # finally, we reset the signal handlers that python screws with back to defaults.
        # gentoo bug #309001, #289486
        for signum in 'SIGPIPE SIGQUIT SIGINT SIGTERM SIGXFS SIGXFZ'.split():
            signum = getattr(signal, signum, None)
            if signum is not None:
                signal.signal(signum, signal.SIG_DFL)

        if self._secondary_preexec is not None:
            self._secondary_preexec()

    @staticmethod
    def _reading_thread(handle, passback):
        try:
            passback.append(handle.read())
        finally:
            handle.close()

    @staticmethod
    def _writing_thread(handle, data):
        try:
            handle.write(data)
        finally:
            handle.close()

    def communicate(self, **inputs):
        inputs = dict((self._write_pipes[handle_name], data)
            for (handle_name, data) in inputs.iteritems() if data)

        jobs = []
        for handle in self._write_pipes.itervalues():
            if handle.closed:
                continue
            data = inputs.pop(handle, None)
            if data is not None:
                jobs.append(partial(self._writing_thread, handle, data))
            elif handle in self._buffered_write_handles:
                # We run this in a thread to ensure that it can't deadlock
                # during the flush for close.
                jobs.append(partial(handle.close))
            else:
                # Close it now since we know it can't deadlock.
                handle.close()

        if inputs:
            raise ValueError("Inputs %r have no matching pipes." % (inputs,))

        collected_data = {}

        # Uniquify this to protect against mixing results if a client
        # fed us duplicate PIPE_R's; stupid client, but better safe than
        # sorry.
        seen = set()
        for handle_name, handle in self._read_pipes.iteritems():
            if handle in seen:
                continue
            seen.add(handle)
            if not handle.closed:
                collected_data[handle_name] = passback = []
                jobs.append(partial(self._reading_thread, handle, passback))

        # We've built up the list of work we need to do.  Thread it only
        # if needed, else run it w/in this thread.
        try:
            if not jobs:
                self.wait()
            elif len(jobs) == 1:
                jobs[0]()
                self.wait()
            else:
                # Leave one job for this thread.
                threads = [Thread(target=job) for job in jobs[1:]]
                try:
                    for thread in threads:
                        thread.start()

                    # Run the job we didn't background.
                    jobs[0]()
                    self.wait()
                finally:
                    for thread in threads:
                        try:
                            thread.join()
                        except RunTimeError:
                            # This can only occur if the thread wasn't yet
                            # started, and an exception occured.
                            pass

        finally:
            self.terminate()

        output = dict((k, v[0]) for k, v in collected_data.iteritems())
        return self.returncode, output

    def send_signal(self, sig):
        if self.returncode is None:
            self._internal_send_signal(sig)

    def _internal_send_signal(self, signum, ESRCH=errno.ESRCH,
                              suppress=EnvironmentError, kill=os.kill):
        # Note this may be invoked from __del__ contexts, thus we need
        # to avoid referencing anything beyond locals.
        try:
            kill(self.pid, signum)
        except suppress, e:
            if e.errno != ESRCH:
                raise

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.terminate()
        self.wait()
        return None

    def __del__(self):
        if not getattr(self, '_child_created', False):
            # If we didn't get this far, then there isn't anything to do.
            return
        # Ok... kill the child then (maximal force; if the process's representing
        # object is being gc'd, we want this dead.
        self.kill()
        self._internal_poll()
        # Explicitly cloes our pipes so that nothing can try to access them,
        # nor the underlying fd.  Just a source of bugs allowing it.
        for handle in self._read_pipes.itervalues():
            handle.close()
        for handle in self._write_pipes.itervalues():
            handle.close()


def spawn_bash(mycommand, debug=False, name=None, **keywords):
    """spawn the command via bash -c"""

    args = [BASH_BINARY, '--norc', '--noprofile']
    if debug:
        # Print commands and their arguments as they are executed.
        args.append("-x")
    args.append("-c")
    if isinstance(mycommand, str):
        args.append(mycommand)
    else:
        args.extend(mycommand)
    if not name:
        name = os.path.basename(args[3])
    return spawn(args, name=name, **keywords)


def spawn_sandbox(mycommand, name=None, **keywords):
    """spawn the command under sandboxed"""

    if not is_sandbox_capable():
        return spawn_bash(mycommand, name=name, **keywords)
    args = [SANDBOX_BINARY]
    if isinstance(mycommand, str):
        args.extend(mycommand.split())
    else:
        args.extend(mycommand)
    if not name:
        name = os.path.basename(args[1])
    return spawn(args, name=name, **keywords)


def spawn(*args, **kwds):
    """Wrapper around process.
    :param wait: controls whether spawn waits for the process to finish,
        or returns the pid.
    :param input: String data to feed to stdin for the process.
    :param inputs: A mapping of fd -> data to feed to the process.
    :return: Either a return code, or if wait is set, the process object."""
    wait = kwds.pop('wait', True)
    stdin = kwds.pop('stdin', None)
    inputs = kwds.pop('inputs', {})
    if stdin is not None:
        inputs['stdin'] = stdin
    p = process(*args, **kwds)
    if wait:
        ret, data = p.communicate(**inputs)
        return process_exit_code(ret)
    return p


def spawn_get_output(command, spawn_type=None, data=None, collect_fds=(1,),
                     **kwds):

    """Call spawn, collecting the output to fd's specified in collect_fds list.

    :param spawn_type: the passed in function to call- typically :func:`spawn_bash`,
       :func:`spawn`, :func:`spawn_sandbox`, or :func:`spawn_fakeroot`.
       Defaults to :func:`spawn`.
    :param data: If given, data to feed to stdin.
    :param collect_fds: Which fds to collect data from.
    :return: A tuple of (return code, data); with data being either a string, or
        a list if split_lines is enabled.  Data is purely what's collected from
        the specified fds.
    """

    if spawn_type is None:
        spawn_type = spawn

    pipe = PIPE_R('output')
    kwds['fd_pipes'] = fd_pipes = dict((x, pipe) for x in collect_fds)
    # Set stdin to /dev/null by default.
    fd_pipes.setdefault(0, None)
    fd_pipes.setdefault(2, None)
    if data:
        fd_pipes[0] = PIPE_W('stdin')
    p = spawn_type(command, wait=False, **kwds)
    ret, results = p.communicate(stdin=data)
    return ret, results['output']


def spawn_fakeroot(command, save_file, env=None, name=None, wait=True, **kwds):
    """spawn a process via fakeroot

    refer to the fakeroot manpage for specifics of using fakeroot
    """
    if env is None:
        env = {}
    else:
        env = ProtectedDict(env)

    if name is None:
        name = "fakeroot %s" % command

    args = [
        FAKED_PATH,
        "--unknown-is-real", "--foreground", "--save-file", save_file]


    fd_pipes = {0:None, 1:PIPE_R('output'), 2:'@1'}
    if os.path.exists(save_file):
        args.append('--load')
        fd_pipes[0] = os.open(save_file, os.O_RDONLY)

    try:
        faked = spawn(args, fd_pipes=fd_pipes)
    finally:
        if fd_pipes[0] is not None:
            os.close(fd_pipes[0])
    line = faked.output.readline().strip()
    faked.output.close()

    try:
        fakekey, fakepid = map(int, line.split(":"))
    except ValueError:
        faked.terminate()
        raise ExecutionFailure("output from faked was unparsable- %s" % line)

    # by now we have our very own daemonized faked.  yay.
    env["FAKEROOTKEY"] = str(fakekey)
    paths = [LIBFAKEROOT_PATH] + env.get("LD_PRELOAD", "").split(":")
    env["LD_PRELOAD"] = ":".join(x for x in paths if x)

    results = None
    try:
        results = spawn(command, name=name, env=env, wait=wait, **kwds)
        if not wait:
            results.faked_daemon = faked
            return results
        faked.terminate()
        return results
    except:
        faked.terminate()
        if results is not None:
            results.terminate()
        faked = results = None


def process_exit_code(retval):
    """Process a waitpid returned exit code.

    :return: The exit code if it exit'd, the signal if it died from signalling.
    """
    # If it got a signal, return the signal that was sent.
    if retval & 0xff:
        return (retval & 0xff) << 8

    # Otherwise, return its exit code.
    return retval >> 8


class ExecutionFailure(Exception):
    def __init__(self, msg):
        Exception.__init__(self, msg)
        self.msg = msg
    def __str__(self):
        return "Execution Failure: %s" % self.msg

# cached capabilities

def is_fakeroot_capable(force=False):
    if not force:
        try:
            return is_fakeroot_capable.cached_result
        except AttributeError:
            pass
    if not (os.path.exists(FAKED_PATH) and os.path.exists(LIBFAKEROOT_PATH)):
        res = False
    else:
        try:
            r, s = spawn_get_output(["fakeroot", "--version"],
                                    collect_fds=(1,2))
            res = (r == 0 and "version 1." in s[0])
        except ExecutionFailure:
            res = False
    is_fakeroot_capable.cached_result = res
    return res

def is_sandbox_capable(force=False):
    if not force:
        try:
            return is_sandbox_capable.cached_result
        except AttributeError:
            pass
    res = os.path.isfile(SANDBOX_BINARY) and access(SANDBOX_BINARY, os.X_OK)
    is_sandbox_capable.cached_result = res
    return res

def is_userpriv_capable(force=False):
    if not force:
        try:
            return is_userpriv_capable.cached_result
        except AttributeError:
            pass
    res = is_userpriv_capable.cached_result = (os.getuid() == 0)
    return res

def find_invoking_python():
    # roughly... use sys.executable if possible, then major ver variations-
    # look for python2.5, python2, then just python, for example
    if os.path.exists(sys.executable):
        return sys.executable
    chunks = list(str(x) for x in sys.version_info[:2])
    for potential in (chunks, chunks[:-1], ''):
        try:
            command_name = 'python%s' % '.'.join(potential)
            return find_binary(command_name)
        except CommandNotFound:
            continue
    raise CommandNotFound('python')
