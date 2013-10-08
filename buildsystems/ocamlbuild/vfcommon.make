#
# Things common for building all VeriFast frontends (vfconsole, vfide)
# The make files for building these frontends can include this file.
# Basically, this file is to avoid code duplication.
#

ifndef VFCOMMON_MAKE_INCLUDED
  VFCOMMON_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make
include z3dependency.make

INCLUDECODE_VFCOMMON += $(SRCDIR)/verifastPluginRedux.ml

ifndef NOZ3
  run_ocamlbuild_vfcommon: z3maybe
  INCLUDECODE_VFCOMMON += $(INCLUDECODE_Z3)
  OCAMLBUILDFLAGS_VFCOMMON += $(OCAMLBUILDFLAGS_Z3)
endif

ifeq ($(OS), linux)
  OCAMLBUILDFLAGS_VFCOMMON+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux
endif
ifeq ($(OS), win)
  OCAMLBUILDFLAGS_VFCOMMON+= -cflags -I,$(SRCDIR)/win -lflags -I,$(SRCDIR)/win
endif
ifeq ($(OS), macos)
  OCAMLBUILDFLAGS_VFCOMMON+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux -I macos
endif

OCAMLBUILDFLAGS_VFCOMMON+= -pp camlp4o.opt -libs Perf,nums,str,dynlink

# For building Java frontend prototype
OCAMLBUILDFLAGS_VFCOMMON+= -I java_frontend -tag thread

run_ocamlbuild_vfcommon: $(OS) vfversion

ifdef BYTECODE
  OCAMLOPTOPT=$(OCAMLC)
  linux_or_macos: ocamlc
else
  OCAMLOPTOPT=$(OCAMLOPT)
  linux_or_macos: ocamlopt
endif
linux_or_macos: make
	make -C $(SRCDIR)/linux OCAMLOPTOPT=$(OCAMLOPTOPT) BYTECODE=$(BYTECODE) DEBUG=$(DEBUG)

vfversion: ocaml
	cd $(SRCDIR) ; ${OCAML} generate_vfversion.ml

linux: linux_or_macos
	cp $(SRCDIR)/Fonts_default.ml $(SRCDIR)/Fonts.ml

macos: linux_or_macos
	cp $(SRCDIR)/Fonts_mac.ml $(SRCDIR)/Fonts.ml

win: ocamlopt
	cd $(SRCDIR)/win ;\
	export CYGWIN=nodosfilewarning ;\
	$(OCAMLOPT) -a -o Perf.cmxa caml_perf.c Perf.mli Perf.ml Stopwatch.mli caml_stopwatch.c
	
clean::
	rm -fr $(BUILDDIR)
	rm -f $(SRCDIR)/linux/*.o
	rm -f $(SRCDIR)/linux/*.a
	rm -f $(SRCDIR)/linux/*.cm*
	rm -f $(SRCDIR)/macos/*.o
	rm -f $(SRCDIR)/macos/*.a
	rm -f $(SRCDIR)/macos/*.cm*
	rm -f $(SRCDIR)/win/*.o
	rm -f $(SRCDIR)/win/*.a
	rm -f $(SRCDIR)/win/*.cm*
	rm -f $(SRCDIR)/win/*.dll

endif
