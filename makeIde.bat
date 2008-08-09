ocamlc.opt -pp camlp4o -warn-error F -g -I +lablgtk2 lablgtk.cma gtkInit.cmo -o vfide.exe unix.cma Verifast.cmo verifast.ml VerifastIDE.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
