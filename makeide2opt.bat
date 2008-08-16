if "%GTKLIB%"=="" goto gtkliberror
ocamlopt.opt -warn-error F -c redux.ml
@if errorlevel 1 goto failed
ocamlopt.opt -pp camlp4o -warn-error F -I +lablgtk2 -ccopt "/link /LIBPATH:%GTKLIB%" lablgtk.cmxa gtkInit.cmx -o vf2ide.opt.exe unix.cmxa redux.cmx verifast2.ml Verifast2IDE.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
@goto done
:gtkliberror
@echo Please set GTKLIB to your GTK installation's lib subdirectory (e.g. "set GTKLIB=C:\gtk\lib")
:done
