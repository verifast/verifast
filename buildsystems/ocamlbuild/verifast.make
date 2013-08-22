ifndef VERIFAST_MAKE_INCLUDED
  VERIFAST_MAKE_INCLUDED = yes

include init.make

verifast: run_ocamlbuild_verifast
verifast: INCLUDECODE+=$(SRCDIR)/verifastPluginRedux.ml
verifast: BINNAME=verifast
verifast: SRCNAME=vfconsole.ml
verifast: OCAMLBUILDFLAGS+=$(OCAMLBUILDFLAGS_vfide_and_verifast)
.PHONY: verifast
OCAMLBUILDSUBTARGETS+=verifast

clean::
	rm -f $(BINDIR)/verifast

endif
