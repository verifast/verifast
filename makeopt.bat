ocamlopt -pp camlp4o -I +labltk -cclib /link -cclib /LIBPATH:\tcl\lib labltk.cmxa -o verifast.exe unix.cmxa verifast.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
