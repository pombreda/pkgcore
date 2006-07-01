# Copyright: 2005 Brian Harring <ferringb@gmail.com>
# License: GPL2

from itertools import imap
from pkgcore.fs import fs

def check_instance(obj):
	if not isinstance(obj, fs.fsBase):
		raise TypeError("'%s' is not a fs.fsBase deriviative" % obj)
	return obj


class contentsSet(set):
	"""class wrapping a contents file"""

	def __new__(cls, *a, **kw):
		# override __new__ so set doesn't scream about opt args
		return set.__new__(cls)

	def __init__(self, initial=None, frozen=False):
		if initial is None:
			initial = []
		set.__init__(self, imap(check_instance, initial))
		self.frozen = frozen

	def add(self, obj):
		if self.frozen:
			# weird, but keeping with set.
			raise AttributeError("%s is frozen; no add functionality" % self.__class__)
		if not isinstance(obj, fs.fsBase):
			raise TypeError("'%s' is not a fs.fsBase class" % str(obj))
		set.add(self, obj)

	def remove(self, obj):
		if self.frozen:
			# weird, but keeping with set.
			raise AttributeError("%s is frozen; no remove functionality" % self.__class__)
		if not isinstance(obj, fs.fsBase):
			# why are we doing the loop and break?  try this
			# s=set([1,2,3]);
			# for x in s:s.remove(x)
			# short version, you can't yank stuff while iterating over the beast.
			# iow, what you think would be cleaner/simpler here, doesn't work. :)
			# ~harring

			if obj is not None:
				for x in self:
					if obj == x.location:
						set.remove(self, x)
						return
			raise KeyError(obj)
		else:
			set.remove(self, obj)

	def __contains__(self, key):
		if isinstance(key, fs.fsBase):
			return set.__contains__(self, key)
		for x in self:
			if key == x.location:
				return True
		return False

	def clear(self):
		if self.frozen:
			# weird, but keeping with set.
			raise AttributeError("%s is frozen; no clear functionality" % self.__class__)
		set.clear(self)

	def iterfiles(self, invert=False):
		return (x for x in self if isinstance(x, fs.fsFile) is not invert)

	def files(self, invert=False):
		return list(self.iterfiles(invert=invert))

	def iterdirs(self, invert=False):
		return (x for x in self if isinstance(x, fs.fsDir) is not invert)

	def dirs(self, invert=False):
		return list(self.iterdirs(invert=invert))

	def iterlinks(self, invert=False):
		return (x for x in self if isinstance(x, fs.fsLink) is not invert)

	def links(self, invert=False):
		return list(self.iterlinks(invert=invert))

	def iterdevs(self, invert=False):
		return (x for x in self if isinstance(x, fs.fsDev) is not invert)

	def devs(self, invert=False):
		return list(self.iterdevs(invert=invert))

	def iterfifos(self, invert=False):
		return (x for x in self if isinstance(x, fs.fsFifo) is not invert)

	def fifos(self, invert=False):
		return list(self.iterfifos(invert=invert))
