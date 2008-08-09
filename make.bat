ocamlc -warn-error F -g -pp camlp4o -I +lablgtk2 lablgtk.cma gtkInit.cmo -o verifast.exe unix.cma verifast.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
