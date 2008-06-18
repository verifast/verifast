ocamlopt -pp camlp4o -o verifast.exe unix.cmxa verifast.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
:done
