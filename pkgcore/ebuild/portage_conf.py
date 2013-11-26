# Copyright: 2006-2011 Brian Harring <ferringb@gmail.com>
# License: GPL2/BSD

"""make.conf translator.

Converts portage configuration files into :obj:`pkgcore.config` form.
"""

__all__ = ("SecurityUpgradesViaProfile", "add_layman_syncers", "make_syncer",
    "add_sets", "add_profile", "add_fetcher", "mk_simple_cache",
    "config_from_make_conf")

import os

from pkgcore.config import basics, configurable
from pkgcore.ebuild import const
from pkgcore.pkgsets.glsa import SecurityUpgrades

from snakeoil.osutils import normpath, abspath, listdir_files, pjoin, ensure_dirs
from snakeoil.compatibility import raise_from
from snakeoil.demandload import demandload
demandload(globals(),
    'errno',
    'pkgcore.config:errors',
    'pkgcore.log:logger',
    'ConfigParser:ConfigParser',
    'snakeoil.bash:read_bash_dict',
    'pkgcore.ebuild:profiles',
    'snakeoil.xml:etree',
)


def my_convert_hybrid(manager, val, arg_type):
    """Modified convert_hybrid using a sequence of strings for section_refs."""
    if arg_type.startswith('refs:'):
        subtype = 'ref:' + arg_type.split(':', 1)[1]
        return list(
            basics.LazyNamedSectionRef(manager, subtype, name)
            for name in val)
    return basics.convert_hybrid(manager, val, arg_type)


@configurable({'ebuild_repo': 'ref:repo', 'vdb': 'ref:repo',
               'profile': 'ref:profile'}, typename='pkgset')
def SecurityUpgradesViaProfile(ebuild_repo, vdb, profile):
    """
    generate a GLSA vuln. pkgset limited by profile

    :param ebuild_repo: :obj:`pkgcore.ebuild.repository.UnconfiguredTree` instance
    :param vdb: :obj:`pkgcore.repository.prototype.tree` instance that is the livefs
    :param profile: :obj:`pkgcore.ebuild.profiles` instance
    """
    arch = profile.arch
    if arch is None:
        raise errors.ComplexInstantiationError("arch wasn't set in profiles")
    return SecurityUpgrades(ebuild_repo, vdb, arch)


def add_layman_syncers(new_config, rsync_opts, overlay_paths, config_root='/',
    default_loc="etc/layman/layman.cfg",
    default_conf='overlays.xml'):

    try:
        f = open(pjoin(config_root, default_loc))
    except IOError, ie:
        if ie.errno != errno.ENOENT:
            raise
        return {}

    c = ConfigParser()
    c.readfp(f)
    storage_loc = c.get('MAIN', 'storage')
    overlay_xml = pjoin(storage_loc, default_conf)
    del c

    try:
        xmlconf = etree.parse(overlay_xml)
    except IOError, ie:
        if ie.errno != errno.ENOENT:
            raise
        return {}
    overlays = xmlconf.getroot()
    if overlays.tag != 'overlays':
        return {}

    new_syncers = {}
    for overlay in overlays.findall('overlay'):
        name = overlay.get('name')
        src_type = overlay.get('type')
        uri = overlay.get('src')
        if None in (src_type, uri, name):
            continue
        path = pjoin(storage_loc, name)
        if not os.path.exists(path):
            continue
        elif path not in overlay_paths:
            continue
        if src_type == 'tar':
            continue
        elif src_type == 'svn':
            if uri.startswith('http://') or uri.startswith('https://'):
                uri = 'svn+' + uri
        elif src_type != 'rsync':
            uri = '%s+%s' % (src_type, uri)

        new_syncers[path] = make_syncer(new_config, path, uri, rsync_opts, False)
    return new_syncers


def isolate_rsync_opts(options):
    """
    pop the misc RSYNC related options littered in make.conf, returning
    a base rsync dict, and the full SYNC config
    """
    base = {}
    extra_opts = []

    extra_opts.extend(options.pop('PORTAGE_RSYNC_EXTRA_OPTS', '').split())

    ratelimit = options.pop('RSYNC_RATELIMIT', None)
    if ratelimit is not None:
        extra_opts.append('--bwlimit=%s' % ratelimit.strip())

    # keep in mind this pops both potential vals.
    retries = options.pop('PORTAGE_RSYNC_RETRIES',
        options.pop('RSYNC_RETRIES', None))
    if retries is not None:
        try:
            retries = int(retries)
            if retries < 0:
                retries = 10000
            base['retries'] = str(retries)
        except ValueError:
            pass

    timeout = options.pop('RSYNC_TIMEOUT', None)
    if timeout is not None:
        base['timeout'] = timeout.strip()

    proxy = options.pop('RSYNC_PROXY', None)
    if proxy is not None:
        base['proxy'] = proxy.strip()

    excludes = options.pop('RSYNC_EXCLUDEFROM', None)
    if excludes is not None:
        extra_opts.extend('--exclude-from=%s' % x
            for x in excludes.split())

    if extra_opts:
        base['extra_opts'] = tuple(extra_opts)

    return base


def make_syncer(new_config, basedir, sync_uri, rsync_opts,
    allow_timestamps=True):
    d = {'basedir': basedir, 'uri': sync_uri}
    if sync_uri.startswith('rsync'):
        d.update(rsync_opts)
        if allow_timestamps:
            d['class'] = 'pkgcore.sync.rsync.rsync_timestamp_syncer'
        else:
            d['class'] = 'pkgcore.sync.rsync.rsync_syncer'
    else:
        d['class'] = 'pkgcore.sync.base.GenericSyncer'

    name = 'sync:%s' % basedir
    new_config[name] = basics.AutoConfigSection(d)
    return name


def make_autodetect_syncer(new_config, basedir):
    name = 'sync:%s' % basedir
    new_config[name] = basics.AutoConfigSection({
        'class':'pkgcore.sync.base.AutodetectSyncer',
        'basedir':basedir})
    return name


def add_sets(config, root, portage_base_dir):
    config["world"] = basics.AutoConfigSection({
            "class": "pkgcore.pkgsets.filelist.WorldFile",
            "location": pjoin(root, const.WORLD_FILE)})
    config["system"] = basics.AutoConfigSection({
            "class": "pkgcore.pkgsets.system.SystemSet",
            "profile": "profile"})
    config["installed"] = basics.AutoConfigSection({
            "class": "pkgcore.pkgsets.installed.Installed",
            "vdb": "vdb"})
    config["versioned-installed"] = basics.AutoConfigSection({
            "class": "pkgcore.pkgsets.installed.VersionedInstalled",
            "vdb": "vdb"})

    set_fp = pjoin(portage_base_dir, "sets")
    try:
        for setname in listdir_files(set_fp):
            # Potential for name clashes here, those will just make
            # the set not show up in config.
            if setname in ("system", "world"):
                logger.warn("user defined set %s is disallowed; ignoring" %
                    pjoin(set_fp, setname))
                continue
            config[setname] = basics.AutoConfigSection({
                    "class":"pkgcore.pkgsets.filelist.FileList",
                    "location":pjoin(set_fp, setname)})
    except OSError, e:
        if e.errno != errno.ENOENT:
            raise

def _find_profile_link(base_path, portage_compat=False):
    make_profile = pjoin(base_path, 'make.profile')
    try:
        return normpath(abspath(
            pjoin(base_path, os.readlink(make_profile))))
    except EnvironmentError, oe:
        if oe.errno in (errno.ENOENT, errno.EINVAL):
            if oe.errno == errno.ENOENT:
                if portage_compat:
                    return None
                profile = _find_profile_link(pjoin(base_path, 'portage'), True)
                if profile is not None:
                    return profile
            raise_from(errors.ComplexInstantiationError(
                "%s must be a symlink pointing to a real target" % (
                    make_profile,)))
        raise_from(errors.ComplexInstantiationError(
            "%s: unexpected error- %s" % (make_profile, oe.strerror)))

def add_profile(config, base_path, user_profile_path=None):
    profile = _find_profile_link(base_path)

    paths = profiles.OnDiskProfile.split_abspath(profile)
    if paths is None:
        raise errors.ComplexInstantiationError(
            '%s expands to %s, but no profile detected' % (
                pjoin(base_path, 'make.profile'), profile))

    if os.path.isdir(user_profile_path):
        config["profile"] = basics.AutoConfigSection({
                "class": "pkgcore.ebuild.profiles.UserProfile",
                "parent_path": paths[0],
                "parent_profile": paths[1],
                "user_path": user_profile_path})
    else:
        config["profile"] = basics.AutoConfigSection({
                "class": "pkgcore.ebuild.profiles.OnDiskProfile",
                "basepath": paths[0],
                "profile": paths[1]})


def add_fetcher(config, conf_dict, distdir):
    fetchcommand = conf_dict.pop("FETCHCOMMAND")
    resumecommand = conf_dict.pop("RESUMECOMMAND", fetchcommand)

    # copy it to prevent modification.
    # map a config arg to an obj arg, pop a few values
    fetcher_dict = dict(conf_dict)
    if "FETCH_ATTEMPTS" in fetcher_dict:
        fetcher_dict["attempts"] = fetcher_dict.pop("FETCH_ATTEMPTS")
    fetcher_dict.pop("readonly", None)
    fetcher_dict.update(
        {"class": "pkgcore.fetch.custom.fetcher",
            "distdir": distdir,
            "command": fetchcommand,
            "resume_command": resumecommand
        })
    config["fetcher"] = basics.AutoConfigSection(fetcher_dict)


def mk_simple_cache(config_root, tree_loc, readonly=False,
    kls='pkgcore.cache.flat_hash.database'):
    readonly = readonly and 'yes' or 'no'
    tree_loc = pjoin(config_root, 'var/cache/edb/dep',
       tree_loc.lstrip('/'))

    return basics.AutoConfigSection({'class': kls,
        'location': tree_loc,
        'readonly': readonly,
        })


def load_make_config(vars_dict, path, allow_sourcing=False, required=True,
    incrementals=False):
    sourcing_command = None
    if allow_sourcing:
        sourcing_command = 'source'
    try:
        new_vars = read_bash_dict(path, vars_dict=vars_dict,
            sourcing_command=sourcing_command)
    except EnvironmentError, ie:
        if ie.errno == errno.EACCES:
            raise_from(errors.PermissionDeniedError(path, write=False))
        if ie.errno != errno.ENOENT or required:
            raise_from(errors.ParsingError("parsing %r" % (path,), exception=ie))
        return

    if incrementals:
        for key in const.incrementals:
            if key in vars_dict and key in new_vars:
                new_vars[key] = "%s %s" % (vars_dict[key], new_vars[key])
    # quirk of read_bash_dict; it returns only what was mutated.
    vars_dict.update(new_vars)


@configurable({'location': 'str'}, typename='configsection')
@errors.ParsingError.wrap_exception("while loading portage configuration")
def config_from_make_conf(location="/etc/"):
    """
    generate a config from a file location

    :param location: location the portage configuration is based in,
        defaults to /etc
    """

    # this actually differs from portage parsing- we allow
    # make.globals to provide vars used in make.conf, portage keeps
    # them separate (kind of annoying)

    config_root = os.environ.get("PORTAGE_CONFIGROOT", "/")
    base_path = pjoin(config_root, location.strip("/"))
    portage_base = pjoin(base_path, "portage")

    # this isn't preserving incremental behaviour for features/use
    # unfortunately

    conf_dict = {}
    try:
        load_make_config(conf_dict, pjoin(base_path, 'make.globals'))
    except errors.ParsingError, e:
        if not getattr(getattr(e, 'exc', None), 'errno', None) == errno.ENOENT:
           raise
        try:
            load_make_config(conf_dict,
                pjoin(config_root, 'usr/share/portage/config/make.globals'))
        except compatibility.IGNORED_EXCEPTIONS:
            raise
        except:
            compatibility.raise_from(errors.ParsingError(
                "failed to find a usable make.globals"))
    load_make_config(conf_dict, pjoin(base_path, 'make.conf'), required=False,
        allow_sourcing=True, incrementals=True)
    load_make_config(conf_dict, pjoin(portage_base, 'make.conf'), required=False,
        allow_sourcing=True, incrementals=True)


    conf_dict.setdefault("PORTDIR", "/usr/portage")
    root = os.environ.get("ROOT", conf_dict.get("ROOT", "/"))
    gentoo_mirrors = list(
        x.rstrip("/")+"/distfiles" for x in conf_dict.pop("GENTOO_MIRRORS", "").split())

    # this is flawed... it'll pick up -some-feature
    features = conf_dict.get("FEATURES", "").split()

    new_config = {}
    triggers = []

    def add_trigger(name, kls_path, **extra_args):
        d = extra_args.copy()
        d['class'] = kls_path
        new_config[name] = basics.ConfigSectionFromStringDict(d)
        triggers.append(name)

    # sets...
    add_sets(new_config, root, portage_base)

    user_profile_path = pjoin(base_path, "portage", "profile")
    add_profile(new_config, base_path, user_profile_path)

    kwds = {"class": "pkgcore.vdb.ondisk.tree",
            "location": pjoin(root, 'var', 'db', 'pkg')}
    kwds["cache_location"] = pjoin(config_root, 'var', 'cache', 'edb',
        'dep', 'var', 'db', 'pkg')
    new_config["vdb"] = basics.AutoConfigSection(kwds)

    portdir = normpath(conf_dict.pop("PORTDIR").strip())
    portdir_overlays = [
        normpath(x) for x in conf_dict.pop("PORTDIR_OVERLAY", "").split()]

    new_config['ebuild-repo-common'] = basics.AutoConfigSection({
            'class': 'pkgcore.ebuild.repository.slavedtree',
            'default_mirrors': gentoo_mirrors,
            'inherit-only': True,
            'ignore_paludis_versioning':
                ('ignore-paludis-versioning' in features),
            })


    # used by PORTDIR syncer, and any layman defined syncers
    rsync_opts = isolate_rsync_opts(conf_dict)
    portdir_syncer = conf_dict.pop("SYNC", None)

    if portdir_overlays and '-layman-sync' not in features:
        overlay_syncers = add_layman_syncers(new_config, rsync_opts,
            portdir_overlays, config_root=config_root)
    else:
        overlay_syncers = {}
    if portdir_overlays and '-autodetect-sync' not in features:
        for path in portdir_overlays:
            if path not in overlay_syncers:
                overlay_syncers[path] = make_autodetect_syncer(new_config, path)

    rsync_portdir_cache = 'metadata-transfer' not in features
    # if a metadata cache exists, use it.
    if rsync_portdir_cache:
        for cache_type, frag in (('flat_hash.md5_cache', 'md5-cache'),
                                 ('metadata.database', 'cache')):
            if not os.path.exists(pjoin(portdir, 'metadata', frag)):
                continue
            new_config["cache:%s/metadata/cache" % (portdir,)] = basics.AutoConfigSection({
                'class': 'pkgcore.cache.' + cache_type,
                'readonly': 'yes',
                'location': portdir,
            })
            break
        else:
            rsync_portdir_cache = False

    for tree_loc in [portdir] + portdir_overlays:
        kwds = {
                'inherit': ('ebuild-repo-common',),
                'raw_repo': ('raw:' + tree_loc),
        }
        cache_name = 'cache:%s' % (tree_loc,)
        new_config[cache_name] = mk_simple_cache(config_root, tree_loc)
        kwds['cache'] = cache_name
        if tree_loc == portdir:
            kwds['class'] = 'pkgcore.ebuild.repository.tree'
            if rsync_portdir_cache:
                kwds['cache'] = 'cache:%s/metadata/cache %s' % (portdir, cache_name)
        else:
            kwds['parent_repo'] = portdir
        new_config[tree_loc] = basics.AutoConfigSection(kwds)

    new_config['portdir'] = basics.section_alias(portdir, 'repo')

    base_portdir_config = {}
    if portdir_syncer is not None:
        make_syncer(new_config, portdir, portdir_syncer, rsync_opts)

    if portdir_overlays:
        new_config['repo-stack'] = basics.FakeIncrementalDictConfigSection(
            my_convert_hybrid, {
                'class': 'pkgcore.repository.multiplex.config_tree',
                'repositories': tuple(reversed([portdir] + portdir_overlays))})
    else:
        new_config['repo-stack'] = basics.section_alias(portdir, 'repo')

    for tree_loc in [portdir] + portdir_overlays:
        conf = {'class':'pkgcore.ebuild.repo_objs.RepoConfig',
             'location':tree_loc}
        if 'sync:%s' % (tree_loc,) in new_config:
            conf['syncer'] = 'sync:%s' % (tree_loc,)
        if tree_loc == portdir:
            conf['default'] = True
        new_config['raw:' + tree_loc] = basics.AutoConfigSection(conf)


    new_config['vuln'] = basics.AutoConfigSection({
            'class': SecurityUpgradesViaProfile,
            'ebuild_repo': 'repo-stack',
            'vdb': 'vdb',
            'profile': 'profile'})
    new_config['glsa'] = basics.section_alias('vuln',
        SecurityUpgradesViaProfile.pkgcore_config_type.typename)
    #binpkg.
    pkgdir = conf_dict.pop('PKGDIR', None)
    default_repos = list(reversed(portdir_overlays)) + [portdir]
    if pkgdir is not None:
        try:
            pkgdir = abspath(pkgdir)
        except OSError, oe:
            if oe.errno != errno.ENOENT:
                raise
            if set(features).intersection(
                ('buildpkg', 'pristine-buildpkg', 'buildsyspkg', 'unmerge-backup')):
                logger.warn("disabling buildpkg related features since PKGDIR doesn't exist")
            pkgdir = None
        else:
            if not ensure_dirs(pkgdir, mode=0755, minimal=True):
                logger.warn("disabling buildpkg related features since PKGDIR either doesn't "
                    "exist, or lacks 0755 minimal permissions")
                pkgdir = None
    else:
       if set(features).intersection(
           ('buildpkg', 'pristine-buildpkg', 'buildsyspkg', 'unmerge-backup')):
           logger.warn("disabling buildpkg related features since PKGDIR is unset")


    # yes, round two; may be disabled from above and massive else block sucks
    if pkgdir is not None:
        if pkgdir and os.path.isdir(pkgdir):
            new_config['binpkg'] = basics.ConfigSectionFromStringDict({
                'class': 'pkgcore.binpkg.repository.tree',
                'location': pkgdir,
                'ignore_paludis_versioning':
                    str('ignore-paludis-versioning' in features)})
            default_repos.append('binpkg')

        if 'buildpkg' in features:
            add_trigger('buildpkg_trigger', 'pkgcore.merge.triggers.SavePkg',
                pristine='no',
                target_repo='binpkg')
        elif 'pristine-buildpkg' in features:
            add_trigger('buildpkg_trigger', 'pkgcore.merge.triggers.SavePkg',
                 pristine='yes',
                target_repo='binpkg')
        elif 'buildsyspkg' in features:
            add_trigger('buildpkg_system_trigger', 'pkgcore.merge.triggers.SavePkgIfInPkgset',
                pristine='yes', target_repo='binpkg', pkgset='system')
        elif 'unmerge-backup' in features:
            add_trigger('unmerge_backup_trigger', 'pkgcore.merge.triggers.SavePkgUnmerging',
                target_repo='binpkg')

    if 'save-deb' in features:
        path = conf_dict.pop("DEB_REPO_ROOT", None)
        if path is None:
            logger.warn("disabling save-deb; DEB_REPO_ROOT is unset")
        else:
            add_trigger('save_deb_trigger', 'pkgcore.ospkg.triggers.SaveDeb',
                basepath=normpath(path), maintainer=conf_dict.pop("DEB_MAINAINER", ''),
                platform=conf_dict.pop("DEB_ARCHITECTURE", ""))

    if 'splitdebug' in features:
        kwds = {}

        if 'compressdebug' in features:
            kwds['compress'] = 'true'

        add_trigger('binary_debug_trigger', 'pkgcore.merge.triggers.BinaryDebug',
            mode='split', **kwds)
    elif 'strip' in features or 'nostrip' not in features:
        add_trigger('binary_debug_trigger', 'pkgcore.merge.triggers.BinaryDebug',
            mode='strip')

    if '-fixlafiles' not in features:
        add_trigger('lafilefixer_trigger',
            'pkgcore.system.libtool.FixLibtoolArchivesTrigger')

    # now add the fetcher- we delay it till here to clean out the environ
    # it passes to the command.
    # *everything* in the conf_dict must be str values also.
    distdir = normpath(conf_dict.pop("DISTDIR", pjoin(portdir, "distdir")))
    add_fetcher(new_config, conf_dict, distdir)

    # finally... domain.
    conf_dict.update({
            'class': 'pkgcore.ebuild.domain.domain',
            'repositories': tuple(default_repos),
            'fetcher': 'fetcher',
            'default': True,
            'vdb': ('vdb',),
            'profile': 'profile',
            'name': 'livefs domain',
            'root':root})

    for f in ("package.mask", "package.unmask", "package.accept_keywords", "package.keywords",
            "package.use", "package.env", "env:ebuild_hook_dir", "bashrc"):
        fp = pjoin(portage_base, f.split(":")[0])
        try:
            os.stat(fp)
        except OSError, oe:
            if oe.errno != errno.ENOENT:
                raise
        else:
            conf_dict[f.split(":")[-1]] = fp

    if triggers:
        conf_dict['triggers'] = tuple(triggers)
    new_config['livefs domain'] = basics.FakeIncrementalDictConfigSection(
        my_convert_hybrid, conf_dict)

    return new_config
