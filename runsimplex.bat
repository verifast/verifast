ocamlc -g -o simplex.exe nums.cma simplex.ml
@if errorlevel 1 goto failed
ocamlrun -b simplex.exe
@goto done
:failed
@echo Failed
:done
