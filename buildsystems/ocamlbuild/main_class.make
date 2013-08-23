#
# Builds "main_class.ml"
#

ifndef MAIN_CLASS_MAKE_INCLUDED
  MAIN_CLASS_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make

main_class: run_ocamlbuild_main_class
main_class: BINNAME=main_class
main_class: SRCNAME=main_class.ml

.PHONY: main_class

clean::
	rm -f $(BINDIR)/main_class$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/main_class

endif
