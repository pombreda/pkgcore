# Copyright: 2005-2011 Brian Harring <ferringb@gmail.com>
# Copyright: 2005 Gentoo Foundation
# License: GPL2

"""
Avoid using- os data- root uid/gid, pkgcore uid/gid, etc.

This will be killed off and bound into configuration subsystem at some point
"""
__all__ = ("ostype", "userland", "xargs", "root_uid", "root_gid", "wheelgid", "secpass",
    "portage_uid", "portage_gid")

import grp
import os
import pwd

ostype = os.uname()[0]

if ostype in ("Linux", "CYGWIN_NT-5.1"):
    userland = "GNU"
    xargs = os.environ["XARGS"] = "xargs -r"
    lchown = os.lchown
elif ostype == "Darwin":
    userland = "Darwin"
    xargs = os.environ["XARGS"] = "xargs"
    def lchown(*pos_args, **key_args):
        pass
elif ostype in ["FreeBSD", "OpenBSD", "NetBSD", "SunOS"]:
    userland = "BSD"
    xargs = os.environ["XARGS"] = "xargs"
    lchown = os.lchown
else:
    raise Exception("Operating system unsupported, '%s'" % ostype)


#os.environ["USERLAND"] = userland

#Secpass will be set to 1 if the user is root or in the portage group.
secpass = 0

uid = os.getuid()
# hard coding sucks.
root_uid = 0
root_gid = wheelgid = 0

if uid == 0:
    secpass = 2
try:
    wheelgid = grp.getgrnam("wheel").gr_gid
    if (not secpass) and (wheelgid in os.getgroups()):
        secpass = 1
except KeyError:
    print "portage initialization: your system doesn't have a 'wheel' group."
    print ("Please fix this as it is a normal system requirement. "
           "'wheel' is GID 10")
    print "'emerge baselayout' and an 'etc-update' should remedy this problem."

#Discover the uid and gid of the portage user/group
try:
    portage_uid = pwd.getpwnam("portage").pw_uid
    portage_gid = grp.getgrnam("portage").gr_gid
    portage_user_groups = tuple(x.gr_name for x in grp.getgrall()
       if 'portage' in x.gr_mem)

    if (secpass == 0):
        secpass = 1
except KeyError:
    portage_uid = 0
    portage_gid = wheelgid
    portage_user_groups = []
    print
    print "'portage' user or group missing. Please update baselayout"
    print "and merge portage user(250) and group(250) into your passwd"
    print "and group files. Non-root compilation is disabled until then."
    print "Also note that non-root/wheel users will need to be added to"
    print "the portage group to do portage commands.\n"
    print "For the defaults, line 1 goes into passwd, and 2 into group."
    print "portage:x:250:250:portage:/var/tmp/portage:/bin/false"
    print "portage::250:portage"
