#
# Builds "dlsymtool.ml"
#

ifndef DLSYMTOOL_MAKE_INCLUDED
  DLSYMTOOL_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make

dlsymtool: run_ocamlbuild_dlsymtool
dlsymtool: BINNAME=dlsymtool
dlsymtool: SRCNAME=dlsymtool.ml

.PHONY: dlsymtool

clean::
	rm -f $(BINDIR)/dlsymtool$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/dlsymtool

endif
