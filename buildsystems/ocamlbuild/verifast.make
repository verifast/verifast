#
# Builds the VeriFast commandline frontend.
#

ifndef VERIFAST_MAKE_INCLUDED
  VERIFAST_MAKE_INCLUDED = yes

include init.make
include vfcommon.make

verifast: run_ocamlbuild_verifast
verifast: INCLUDECODE+=$(INCLUDECODE_VFCOMMON)
verifast: BINNAME=verifast
verifast: SRCNAME=vfconsole.ml
verifast: OCAMLBUILDFLAGS+=$(OCAMLBUILDFLAGS_VFCOMMON)
run_ocamlbuild_verifast: run_ocamlbuild_vfcommon

.PHONY: verifast

clean::
	rm -f $(BINDIR)/verifast$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/verifast

endif
