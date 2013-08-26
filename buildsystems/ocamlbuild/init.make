#
# Basic initialization that every other make file needs.
# Mainly to prevent having to write multiple includes in front of
# every makefile.
#

ifndef INIT_MAKE_INCLUDED
  INIT_MAKE_INCLUDED = yes

-include settings.make

include internalconfig.make
include osdetect.make
include dependencyerrors.make

endif
