# Copyright: 2005-2011 Brian Harring <ferringb@gmail.com>
# License: GPL2/BSD

__all__ = ("bz2_data_source", "tree", "ConfiguredTree")

import os, stat, errno

from pkgcore.repository import prototype, errors
from pkgcore.vdb import virtuals
from pkgcore.plugin import get_plugin
from snakeoil import data_source
from pkgcore.repository import multiplex
from pkgcore.config import ConfigHint
#needed to grab the PN
from pkgcore.ebuild.cpv import versioned_CPV
from pkgcore.ebuild import ebuild_built
from pkgcore.ebuild.errors import InvalidCPV

from snakeoil.osutils import pjoin
from snakeoil.mappings import IndeterminantDict
from snakeoil.currying import partial
from snakeoil.osutils import listdir_dirs
from snakeoil.fileutils import readfile, readfile_bytes
from snakeoil import klass, compatibility, compression
from snakeoil.demandload import demandload
demandload(globals(),
    'pkgcore.vdb:repo_ops',
    'pkgcore.vdb.contents:ContentsFile',
    'pkgcore.log:logger',
)


class bz2_data_source(data_source.base):

    # XXX might want to rebase this to data_source.data_source...

    __slots__ = ("location", "mutable")

    def __init__(self, location, mutable=False):
        data_source.base.__init__(self)
        self.location = location
        self.mutable = mutable

    def text_fileobj(self, writable=False):
        data = compression.decompress_data('bzip2',
            readfile_bytes(self.location)).decode()
        if writable:
            if not self.mutable:
                raise TypeError("data source %s is not mutable" % (self,))
            return data_source.text_wr_StringIO(self._set_data, data)
        return data_source.text_ro_StringIO(data)

    def bytes_fileobj(self, writable=False):
        data = compression.decompress_data('bzip2',
            readfile_bytes(self.location))
        if writable:
            if not self.mutable:
                raise TypeError("data source %s is not mutable" % (self,))
            return data_source.bytes_wr_StringIO(self._set_data, data)
        return data_source.bytes_ro_StringIO(data)

    def _set_data(self, data):
        if compatibility.is_py3k:
            if isinstance(data, str):
                data = data.encode()
        open(self.location, "wb").write(
            compression.compress_data('bzip2', data))


class tree(prototype.tree):
    livefs = True
    configured = False
    configurables = ("domain", "settings")
    configure = None
    package_factory = staticmethod(ebuild_built.generate_new_factory)
    operations_kls = repo_ops.operations

    pkgcore_config_type = ConfigHint({'location': 'str',
        'cache_location': 'str', 'repo_id':'str',
        'disable_cache': 'bool'}, typename='repo')

    def __init__(self, location, cache_location=None, repo_id='vdb',
        disable_cache=False):
        prototype.tree.__init__(self, frozen=False)
        self.repo_id = repo_id
        self.location = location
        if disable_cache:
            cache_location = None
        elif cache_location is None:
            cache_location = pjoin("/var/cache/edb/dep",
                location.lstrip("/"))
        self.cache_location = cache_location
        self._versions_tmp_cache = {}
        try:
            st = os.stat(self.location)
            if not stat.S_ISDIR(st.st_mode):
                raise errors.InitializationError(
                    "base not a dir: %r" % self.location)
            elif not st.st_mode & (os.X_OK|os.R_OK):
                raise errors.InitializationError(
                    "base lacks read/executable: %r" % self.location)

        except OSError:
            compatibility.raise_from(errors.InitializationError(
                "lstat failed on base %r" % self.location))

        self.package_class = self.package_factory(self)

    def _get_categories(self, *optional_category):
        # return if optional_category is passed... cause it's not yet supported
        if optional_category:
            return {}
        try:
            try:
                return tuple(x for x in listdir_dirs(self.location) if not
                             x.startswith('.'))
            except EnvironmentError, e:
                compatibility.raise_from(KeyError("failed fetching categories: %s" % str(e)))
        finally:
            pass

    def _get_packages(self, category):
        cpath = pjoin(self.location, category.lstrip(os.path.sep))
        l = set()
        d = {}
        bad = False
        try:
            for x in listdir_dirs(cpath):
                if x.startswith(".tmp.") or x.endswith(".lockfile") \
                    or x.startswith("-MERGING-"):
                    continue
                try:
                    pkg = versioned_CPV(category+"/"+x)
                except InvalidCPV:
                    bad = True
                if bad or not pkg.fullver:
                    if '-scm' in x:
                        bad = 'scm'
                    elif '-try' in x:
                        bad = 'try'
                    else:
                        raise InvalidCPV("%s/%s: no version component" %
                            (category, x))
                    logger.error("merged -%s pkg detected: %s/%s. "
                        "throwing exception due to -%s not being a valid"
                        " version component.  Silently ignoring that "
                        "specific version is not viable either since it "
                        "would result in pkgcore stomping whatever it was "
                        "that -%s version merged.  "
                        "This is why embrace and extend is bad, mm'kay.  "
                        "Use the offending pkg manager that merged it to "
                        "unmerge it." % (bad, category, x, bad, bad))
                    raise InvalidCPV("%s/%s: -%s version component is "
                        "not standard." % (category, x, bad))
                l.add(pkg.package)
                d.setdefault((category, pkg.package), []).append(pkg.fullver)
        except EnvironmentError, e:
            compatibility.raise_from(KeyError("failed fetching packages for category %s: %s" % \
            (pjoin(self.location, category.lstrip(os.path.sep)), str(e))))

        self._versions_tmp_cache.update(d)
        return tuple(l)

    def _get_versions(self, catpkg):
        return tuple(self._versions_tmp_cache.pop(catpkg))

    def _get_ebuild_path(self, pkg):
        s = "%s-%s" % (pkg.package, pkg.fullver)
        return pjoin(self.location, pkg.category, s, s+".ebuild")

    def _get_path(self, pkg):
        s = "%s-%s" % (pkg.package, pkg.fullver)
        return pjoin(self.location, pkg.category, s)

    _metadata_rewrites = {
        "depends":"DEPEND", "rdepends":"RDEPEND", "post_rdepends":"PDEPEND",
        "use":"USE", "eapi":"EAPI", "CONTENTS":"contents", "provides":"PROVIDE",
        "source_repository":"repository", "fullslot":"SLOT"
    }

    def _get_metadata(self, pkg):
        return IndeterminantDict(partial(self._internal_load_key,
            pjoin(self.location, pkg.category,
                "%s-%s" % (pkg.package, pkg.fullver))))

    def _internal_load_key(self, path, key):
        key = self._metadata_rewrites.get(key, key)
        if key == "contents":
            data = ContentsFile(pjoin(path, "CONTENTS"), mutable=True)
        elif key == "environment":
            fp = pjoin(path, key)
            if not os.path.exists(fp+".bz2"):
                if not os.path.exists(fp):
                    # icky.
                    raise KeyError("environment: no environment file found")
                data = data_source.local_source(fp)
            else:
                data = bz2_data_source(fp+".bz2")
        elif key == "ebuild":
            fp = pjoin(path,
                os.path.basename(path.rstrip(os.path.sep))+".ebuild")
            data = data_source.local_source(fp)
        elif key == 'repo':
            # try both, for portage/paludis compatibility.
            data = readfile(pjoin(path, 'repository'), True)
            if data is None:
                data = readfile(pjoin(path, 'REPOSITORY'), True)
                if data is None:
                    raise KeyError(key)
        else:
            data = readfile(pjoin(path, key), True)
            if data is None:
                raise KeyError((path, key))
        return data

    def notify_remove_package(self, pkg):
        remove_it = len(self.packages[pkg.category]) == 1
        prototype.tree.notify_remove_package(self, pkg)
        if remove_it:
            try:
                os.rmdir(pjoin(self.location, pkg.category))
            except OSError, oe:
                if oe.errno != errno.ENOTEMPTY:
                    raise
                # silently swallow it;
                del oe

    def __str__(self):
        return '%s.%s: location %s' % (
            self.__class__.__module__, self.__class__.__name__, self.location)


class ConfiguredTree(multiplex.tree):

    livefs = True
    frozen_settable = False

    def __init__(self, raw_vdb, domain, domain_settings):
        self.domain = domain
        self.domain_settings = domain_settings
        self.raw_vdb = raw_vdb
        if raw_vdb.cache_location is not None:
            self.old_style_virtuals = virtuals.caching_virtuals(raw_vdb,
                raw_vdb.cache_location)
        else:
            self.old_style_virtuals = virtuals.non_caching_virtuals(raw_vdb)
        multiplex.tree.__init__(self, raw_vdb, self.old_style_virtuals)

    frozen = klass.alias_attr("raw_vdb.frozen")

tree.configure = ConfiguredTree
