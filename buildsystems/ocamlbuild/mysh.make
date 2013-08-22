ifndef MYSH_MAKE_INCLUDED
  MYSH_MAKE_INCLUDED = yes

include init.make

mysh: $(OS) ocamlopt
	cd $(SRCDIR); ${OCAMLOPT} -thread -o ../bin/mysh unix.cmxa threads.cmxa Fonts.ml mysh.ml
.PHONY: mysh


endif
