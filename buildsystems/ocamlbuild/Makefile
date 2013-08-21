#
# This file contains a buildsystem to build VeriFast and vfide
# 
# It does not build ocaml, GTK, GTK bindings, etc. They ship their
# own buildsystems so you can use that.
#
# Usage: 
#     make verifast     Builds VeriFast
#     make vfide        Builds vfide
#     make stdlib       Builds bin/*.vfmanifest files
#     make all          Builds verifast,vfide,stdlib
#     make              Same as "make all"
#
#     make clean        Removes temporary and output files
# 
# Tip: use option "-j" to enable parallelism, , e.g. "make -j all"
#


# BEGIN Initialization--------------------------------------------------
#
# You're not supposed to put your config in here. If you install
# your stuff properly, everything is autodetected. If you did not
# install properly, the solution is to install properly, not to mess
# up the build system :)
#
BUILDSCRIPTDIR := $(CURDIR)
SRCDIR    := $(BUILDSCRIPTDIR)/../../src
BINDIR    := $(BUILDSCRIPTDIR)/../../bin
BUILDDIR  := $(BUILDSCRIPTDIR)/_tempbuildfiles
OCAMLOPT  ?= $(shell which ocamlopt)
OCAMLBUILD?= $(shell which ocamlbuild)
ifeq ($(shell uname -s), Linux)
	OS ?= linux
endif
ifeq ($(shell uname -s), Darwin)
	OS ?= mac
endif
ifeq ($(OS),)
  ifeq ($(shell uname -o), Cygwin)
    OS ?= win
  endif
endif
# END Initialization----------------------------------------------------


# BEGIN buildsystemdebug------------------------------------------------
#OCAMLBUILDFLAGS+=-classic-display
.SILENT:
# Do not print any warnings for prettier output: TODO: some warnings must be errors.
OCAMLBUILDFLAGS+= -cflags -warn-error,F,-w,-A
# END   buildsystemdebug------------------------------------------------


# BEGIN Checks----------------------------------------------------------
ifeq ($(findstring $(OS), linux mac win),)
  $(error Cannot autodetect your system. Please set the environment var OS to linux mac or win in lowercase)
endif
ifeq ($(wildcard $(OCAMLOPT)),)
  $(error Cannot find ocamlopt. Just add its path to the PATH environment variable.)
endif
ifeq ($(wildcard $(OCAMLBUILD)),)
  $(error Cannot find ocamlbuild. Just add its path to the PATH environment variable.)
endif
# END Checks------------------------------------------------------------


ifeq ($(OS), linux)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux
endif
ifeq ($(OS), win)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/win -lflags -I,$(SRCDIR)/win
endif
ifeq ($(OS), mac)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux
endif

default: all
all: verifast vfide stdlib

clean_external:
	rm -f $(wildcard $(addprefix $(SRCDIR)/, *.cmx *.o *.a))

linux_or_mac:
	make -C $(SRCDIR)/linux OCAMLOPTOPT=$(OCAMLOPT)

linux: linux_or_mac
	cp $(SRCDIR)/Fonts_default.ml $(SRCDIR)/Fonts.ml

mac: linux_or_mac
	cp $(SRCDIR)/Fonts_mac.ml $(SRCDIR)/Fonts.ml

OCAMLBUILDFLAGS+= -j 32 -no-hygiene -lflags -I,$(SRCDIR)/$(OS) -pp camlp4o.opt
OCAMLBUILDFLAGS_vfide_and_verifast+= -libs Perf,nums,dynlink

vfide: OCAMLBUILDFLAGS+=-use-ocamlfind -pkgs lablgtk2 -libs unix,lablgtksourceview2 $(OCAMLBUILDFLAGS_vfide_and_verifast)
vfide: run_ocamlbuild_vfide
vfide: BINNAME=vfide
vfide: SRCNAME=vfide.ml
vfide: INCLUDECODE+=$(SRCDIR)/verifastPluginRedux.ml
OCAMLBUILDSUBTARGETS+=vfide

verifast: run_ocamlbuild_verifast
verifast: INCLUDECODE+=$(SRCDIR)/verifastPluginRedux.ml
verifast: BINNAME=verifast
verifast: SRCNAME=vfconsole.ml
verifast: OCAMLBUILDFLAGS+=$(OCAMLBUILDFLAGS_vfide_and_verifast)
OCAMLBUILDSUBTARGETS+=verifast

$(addprefix run_ocamlbuild_,$(OCAMLBUILDSUBTARGETS)): clean_external linux
	cat $(INCLUDECODE) $(SRCDIR)/$(SRCNAME) > $(SRCDIR)/buildcat_$(BINNAME).ml ;\
	mkdir -p $(BUILDDIR) ;\
	cd $(SRCDIR) ;\
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) -build-dir $(BUILDDIR)/$(BINNAME) buildcat_$(BINNAME).native;\
	cp $(BUILDDIR)/$(BINNAME)/buildcat_$(BINNAME).native $(BINDIR)/$(BINNAME)

run_ocamlbuild:
	$(error Internal error: target run_ocamlbuild must not be used, use run_ocamlbuild_SUBTARGETNAME)

clean:
	rm -fr $(BUILDDIR)
	rm -f $(BINDIR)/vfide
	rm -f $(BINDIR)/verifast
	rm -f $(SRCDIR)/buildcat_*.ml
	rm -f $(addprefix $(BINDIR)/, $(STDLIB_FILES_VFMANIFEST))
	
.PHONY: default clean_external linux_or_mac linux mac mysh vfide verifast run_ocamlbuild

# BEGIN stdlib----------------------------------------------------------
STDLIB_FILES:=list listex arrays raw_ghost_lists quantifiers permutations assoclist
STDLIB_FILES_VFMANIFEST:=$(addsuffix .vfmanifest,$(STDLIB_FILES))
STDLIB_FILES_C:=$(addsuffix .c,$(STDLIB_FILES))

.PHONY: $(STDLIB_FILES)

$(STDLIB_FILES_C): %.c: $(BINDIR)/%.c
$(STDLIB_FILES_VFMANIFEST): %.vfmanifest: %.c verifast
	cd $(BINDIR) ; ./verifast -c -emit_vfmanifest $<

stdlib: $(STDLIB_FILES_VFMANIFEST)
# END stdlib------------------------------------------------------------


