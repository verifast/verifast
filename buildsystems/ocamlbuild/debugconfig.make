ifndef DEBUGCONFIG_MAKE_INCLUDED
  DEBUGCONFIG_MAKE_INCLUDED = yes

#OCAMLBUILDFLAGS+=-classic-display
.SILENT:
# Do not print any warnings for prettier output: TODO: some warnings must be errors.
OCAMLBUILDFLAGS+= -cflags -warn-error,F,-w,-A


endif
