ocamlc.opt -warn-error F -g -pp camlp4o -o verifast.exe unix.cma verifast.ml VerifastConsole.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
