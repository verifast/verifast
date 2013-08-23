#
# Detection of which operating system the user of the buildsystem uses.
#

ifndef OSDETECT_MAKE_INCLUDED
  OSDETECT_MAKE_INCLUDED = yes

ifeq ($(shell uname -s), Linux)
  OS = linux
endif
ifeq ($(shell uname -s), Darwin)
  OS = macos
endif
ifeq ($(shell uname -o), Msys)
  OS = win
endif
ifeq ($(shell uname -o), Cygwin)
  OS = win
endif


ifeq ($(OS), win)
  DOTEXE = .exe
endif

ifeq ($(findstring $(OS), linux macos win),)
  $(error Cannot autodetect your system. It might be unsupported.)
endif

endif
