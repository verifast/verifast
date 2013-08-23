#
# Builds "java_card_applet.ml"
#

ifndef JAVA_CARD_APPLET_MAKE_INCLUDED
  JAVA_CARD_APPLET_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make

java_card_applet: run_ocamlbuild_java_card_applet
java_card_applet: BINNAME=java_card_applet
java_card_applet: SRCNAME=java_card_applet.ml

.PHONY: java_card_applet

clean::
	rm -f $(BINDIR)/java_card_applet$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/java_card_applet

endif
