ocamlc.opt -warn-error F -g -c redux.ml
@if errorlevel 1 goto failed
ocamlc.opt -warn-error F -g -pp camlp4o -o verifast2.exe unix.cma redux.cmo verifast2.ml Verifast2Console.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
