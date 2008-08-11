ocamlopt.opt -warn-error F -pp camlp4o -o verifast.opt.exe unix.cmxa verifast.ml VerifastConsole.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
