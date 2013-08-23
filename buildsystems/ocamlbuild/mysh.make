#
# Building the mysh tool.
#

ifndef MYSH_MAKE_INCLUDED
  MYSH_MAKE_INCLUDED = yes

include init.make
include run_ocamlbuild.make

# ocamlopt has trouble finding files on Windows, ocamlbuild works, so that's why
# we build mysh now with ocamlbuild.

mysh: run_ocamlbuild_mysh
mysh: BINNAME=mysh
mysh: SRCNAME=mysh.ml
mysh: OCAMLBUILDFLAGS += -cflag -thread -lflag -thread -libs unix,threads
mysh: OCAMLBUILD_SUBTARGETS+=$(OS)

.PHONY: mysh

clean::
	rm -f $(BINDIR)/mysh$(DOTEXE)
#	Prevent cygwin/mingw to try launch an ELF executable:
	rm -f $(BINDIR)/mysh

endif
