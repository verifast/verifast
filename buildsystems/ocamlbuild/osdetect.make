ifndef OSDETECT_MAKE_INCLUDED
  OSDETECT_MAKE_INCLUDED = yes

ifeq ($(shell uname -s), Linux)
	OS ?= linux
endif
ifeq ($(shell uname -s), Darwin)
	OS ?= macos
endif
ifeq ($(OS),)
  ifeq ($(shell uname -o), Cygwin)
    OS ?= win
  endif
endif

ifeq ($(findstring $(OS), linux macos win),)
  $(error Cannot autodetect your system.)
endif


endif
