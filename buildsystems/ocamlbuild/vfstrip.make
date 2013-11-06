#
# Building the vfstrip tool.
#

ifndef VFSTRIP_MAKE_INCLUDED
  VFSTRIP_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make

vfstrip: run_ocamlbuild_vfstrip
vfstrip: BINNAME=vfstrip
vfstrip: SRCNAME=vfstrip.ml

.PHONY: vfstrip

clean::
	rm -f $(BINDIR)/vfstrip$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/vfstrip

endif
