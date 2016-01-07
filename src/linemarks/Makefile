ifeq ($(shell uname -o), Cygwin)
DOTEXE=.exe
LABLGTK2=site-lib/lablgtk2
else
DOTEXE=
LABLGTK2=lablgtk2
endif

hello$(DOTEXE): hello.ml linemarks.cmxa
	${OCAMLOPT} ${OCAMLCFLAGS} -o hello$(DOTEXE) -I +$(LABLGTK2) lablgtk.cmxa lablgtksourceview2.cmxa linemarks.cmxa gtkInit.cmx hello.ml

linemarks.cmxa: liblinemarks.a
ifeq ($(shell uname -o), Cygwin)
	${OCAMLOPT} ${OCAMLCFLAGS} -a -o linemarks.cmxa -I +$(LABLGTK2) GtkLineMarks.mli GLineMarks.ml -cclib -L$(shell pwd) -cclib -llinemarks -cclib "`pkg-config --libs gtksourceview-2.0`"
else
	${OCAMLOPT} ${OCAMLCFLAGS} -a -o linemarks.cmxa $(LABLGTK_FLAGS) GtkLineMarks.mli GLineMarks.ml -cclib -L$(shell pwd) -cclib -llinemarks -cclib "`pkg-config --libs gtksourceview-2.0`"
endif

liblinemarks.a: linemarks.o
	ar r liblinemarks.a linemarks.o ml_GtkLineMarks.o

linemarks.o: linemarks.c
	${OCAMLOPT} ${OCAMLCFLAGS} -c -ccopt "`pkg-config --cflags gtksourceview-2.0`" linemarks.c ml_GtkLineMarks.c

ifeq ($(shell valac --version &>/dev/null ; echo $$?), 0)

linemarks.c: linemarks.vala
	valac --vapidir . -C -H linemarks.h --pkg gtksourceview-2.0 --pkg mystuff linemarks.vala

clean::
	rm -f linemarks.c

else

linemarks.c: linemarks.vala
	@echo linemarks.vala is newer than linemarks.c, but no Vala compiler present. Touch linemarks.c to eliminate this message.

endif

clean::
	rm -f *.o *.a *.cm* hello$(DOTEXE)
