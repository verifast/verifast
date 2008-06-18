ocamlc -g -pp camlp4o -o verifast.exe unix.cma verifast.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
