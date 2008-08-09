@setlocal
@set VFPATH=%~dp0
@set TARGET=%~f1
pushd %VFPATH%
ocamlrun -b verifast.exe %TARGET%
popd
