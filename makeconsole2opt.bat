ocamlopt.opt -warn-error F -c redux.ml
@if errorlevel 1 goto failed
ocamlopt.opt -warn-error F -pp camlp4o -o verifast2.opt.exe unix.cmxa redux.cmx verifast2.ml Verifast2Console.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
