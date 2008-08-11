if "%GTKLIB%"=="" goto gtkliberror
ocamlopt.opt -pp camlp4o -warn-error F -I +lablgtk2 -ccopt "/link /LIBPATH:%GTKLIB%" lablgtk.cmxa gtkInit.cmx -o vfide.opt.exe unix.cmxa verifast.ml VerifastIDE.ml
@if errorlevel 1 goto failed
@echo Success
@goto done
:failed
@echo Failed
@goto done
:gtkliberror
@echo Please set GTKLIB to your GTK installation's lib subdirectory (e.g. "set GTKLIB=C:\gtk\lib")
:done
