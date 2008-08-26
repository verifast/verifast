ocamlc.opt -warn-error F -g -c proverapi.ml
@if errorlevel 1 goto failed
ocamlc.opt -warn-error F -g -c proverapi.cmo redux.ml
@if errorlevel 1 goto failed
ocamlc.opt -warn-error F -g -c -I C:\z3-1.3.6\ocaml z3.cmx proverapi.cmo z3prover.ml
@if errorlevel 1 goto failed
ocamlc.opt -warn-error F -g -pp camlp4o -o verifast2.exe -I C:\z3-1.3.6\ocaml z3.cmx unix.cma proverapi.cmo redux.cmo verifast2.ml Verifast2Console.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
