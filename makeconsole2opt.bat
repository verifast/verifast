ocamlopt.opt -warn-error F -c proverapi.ml
@if errorlevel 1 goto failed
ocamlopt.opt -warn-error F -c proverapi.cmx redux.ml
@if errorlevel 1 goto failed
ocamlopt.opt -warn-error F -pp camlp4o -o verifast2.opt.exe unix.cmxa proverapi.cmx redux.cmx verifast2.ml Verifast2Console.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
