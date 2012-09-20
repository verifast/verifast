# Note: Do not use executable names with dots in them. (See <http://caml.inria.fr/mantis/view.php?id=4719>.)

PATH=$(MAKEDIR)\..\bin;$(PATH)
OPT_OPTIONS=-g

test: ..\bin\verifast.exe ..\bin\vfide.exe ..\bin\mysh.exe ..\bin\main_class.exe ..\bin\java_card_applet.exe ..\bin\dlsymtool.exe ..\bin\vfstrip.exe ..\bin\list.vfmanifest ..\bin\raw_ghost_lists.vfmanifest ..\bin\listex.vfmanifest ..\bin\arrays.vfmanifest ..\bin\quantifiers.vfmanifest ..\bin\assoclist.vfmanifest
	time < nl.txt
	cd ..
	cd examples\plugin
	nmake clean
	nmake
	cd ..\..
	mysh -cpus %NUMBER_OF_PROCESSORS% < testsuite.mysh
	cd src
	time < nl.txt

# Verify the shipped modules with Redux so that we know the Mac build works

..\bin\list.vfmanifest: ..\bin\list.gh ..\bin\list.c
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest list.c
	cd ..\src

..\bin\raw_ghost_lists.vfmanifest: ..\bin\raw_ghost_lists.gh ..\bin\raw_ghost_lists.c ..\bin\list.vfmanifest
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest raw_ghost_lists.c
	cd ..\src

..\bin\listex.vfmanifest: ..\bin\listex.gh ..\bin\listex.c ..\bin\list.vfmanifest
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest listex.c
	cd ..\src

..\bin\arrays.vfmanifest: ..\bin\arrays.gh ..\bin\arrays.c ..\bin\list.vfmanifest
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest arrays.c
	cd ..\src

..\bin\quantifiers.vfmanifest: ..\bin\quantifiers.gh ..\bin\quantifiers.c
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest quantifiers.c
	cd ..\src
	
..\bin\assoclist.vfmanifest: ..\bin\assoclist.gh ..\bin\assoclist.c
	cd ..\bin
	verifast -prover redux -c -emit_vfmanifest assoclist.c
	cd ..\src

clean:
	del *.cm* *.obj ..\bin\*.exe win\*.cm* win\*.obj ..\bin\list.vfmanifest ..\bin\raw_ghost_lists.vfmanifest ..\bin\lstex.vfmanifest ..\bin\arrays.vfmanifest

refman:
	cd ..\doc\refman
	pdflatex refman.tex
	pdflatex refman.tex
	pdflatex refman.tex
	cd ..\..\src

cmo: Fonts.cmo Printexc_proxy.cmo record_backtrace.cmo vfversion_cmo Fonts.cmo verifast.cmo simplex.cmo proverapi.cmo redux.cmo z3prover.cmo SExpressions.cmo SExpressionEmitter.cmo

cmx: Fonts.cmx Printexc_proxy.cmx record_backtrace.cmx vfversion_cmx Fonts.cmx verifast.cmx simplex.cmx proverapi.cmx redux.cmx z3prover.cmx SExpressions.cmx SExpressionEmitter.cmx

tabhunter.exe: tabhunter.ml
	ocamlc -o tabhunter.exe tabhunter.ml

tabhunt: tabhunter.exe
	tabhunter.exe

..\bin\vfstrip.exe: vfstrip.ml
	ocamlopt.opt -o ..\bin\vfstrip.exe vfstrip.ml

..\bin\main_class.exe: main_class.ml
	ocamlopt.opt -o ..\bin\main_class.exe main_class.ml

..\bin\java_card_applet.exe: java_card_applet.ml
	ocamlopt.opt -o ..\bin\java_card_applet.exe java_card_applet.ml

..\bin\dlsymtool.exe: dlsymtool.ml
	ocamlopt.opt -o ..\bin\dlsymtool.exe dlsymtool.ml

Fonts.cmo: Fonts_default.ml
	copy Fonts_default.ml Fonts.ml
	ocamlc -c Fonts.ml

Fonts.cmx: Fonts_default.ml
	copy Fonts_default.ml Fonts.ml
	ocamlopt.opt -c Fonts.ml

..\bin\mysh.exe: Fonts.cmx mysh.ml
	ocamlopt.opt -thread -o ..\bin\mysh.exe unix.cmxa threads.cmxa Fonts.cmx mysh.ml

pa_verifast.cmo: pa_verifast.ml
	ocamlc -I +camlp4 dynlink.cma camlp4lib.cma -pp "camlp4o pa_extend.cmo q_MLast.cmo" pa_verifast.ml

Printexc_proxy.cmo:
	copy Printexc_proxy_311.ml Printexc_proxy.ml
	ocamlc -c Printexc_proxy.ml

Printexc_proxy.cmx:
	copy Printexc_proxy_311.ml Printexc_proxy.ml
	ocamlopt.opt -c Printexc_proxy.ml

record_backtrace.cmo: record_backtrace.ml
	ocamlc.opt -c record_backtrace.ml

record_backtrace.cmx: record_backtrace.ml
	ocamlopt.opt -c record_backtrace.ml

vfversion.cmi: vfversion.mli
	ocamlc -c vfversion.mli

vfversion_cmo: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlc -c vfversion.ml

vfversion_cmx: vfversion.cmi
	ocaml generate_vfversion.ml
	ocamlopt.opt $(OPT_OPTIONS) -c vfversion.ml

verifastRedux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -warn-error F -w p -g -pp camlp4o -o verifastRedux.exe unix.cma proverapi.cmo nums.cma simplex.cmo redux.cmo vfversion.cmo verifast.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3Redux.exe: vfversion_cmo proverapi.cmo simplex.cmo redux.cmo z3prover.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlc -custom -warn-error F -g -pp camlp4o -o verifast.exe -I $(Z3)\ocaml unix.cma $(Z3)\ocaml\z3.cma proverapi.cmo nums.cma simplex.cmo redux.cmo z3prover.cmo vfversion.cmo verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

verifastZ3.exe: record_backtrace.cmo vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml
	ocamlc -custom -warn-error F -w p -g -pp camlp4o -o verifastZ3.exe -I $(Z3)\ocaml record_backtrace.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfconsole.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib

vfideZ3.exe: record_backtrace.cmo vfversion_cmo proverapi.cmo z3prover.cmo verifast.cmo verifastPluginZ3.ml vfide.ml
	time < nl.txt
	ocamlc -custom -warn-error F -g -pp camlp4o -o vfideZ3.exe -I $(Z3)\ocaml -I +lablgtk2 record_backtrace.cmo lablgtk.cma gtkInit.cmo unix.cma nums.cma $(Z3)\ocaml\z3.ml proverapi.cmo z3prover.cmo vfversion.cmo verifast.cmo verifastPluginZ3.ml vfide.ml $(Z3)\ocaml\z3_stubs.obj $(Z3)\bin\z3.lib $(OCAMLLIB)\libcamlidl.lib ole32.lib -cclib "-L "$(GTKLIB)
	time < nl.txt

vfide.cmx: vfversion.cmi verifast.cmx Fonts.cmx vfide.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I +lablgtk2 Fonts.cmx vfide.ml
	time < nl.txt

..\bin\vfide.exe: Printexc_proxy.cmx record_backtrace.cmx vfversion_cmx proverapi.cmx z3prover.cmx simplex.cmx redux.cmx DynType.cmx plugins.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx verifastPluginZ3.ml Fonts.cmx vfide.cmx
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error FSU -pp camlp4o -o ..\bin\vfide.exe -I $(Z3)\ocaml -I +lablgtk2 -I .\win record_backtrace.cmx lablgtk.cmxa lablgtksourceview2.cmxa libgtksourceview-2.0-0.lib gtkInit.cmx unix.cmxa nums.cmxa z3.cmxa Perf.cmxa Printexc_proxy.cmx proverapi.cmx z3prover.cmx simplex.cmx redux.cmx vfversion.cmx Dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx verifastPluginRedux.ml verifastPluginZ3.ml Fonts.cmx vfide.cmx -cclib "-L "$(GTKLIB)
	time < nl.txt

vfideredux.exe: Printexc_proxy.cmx record_backtrace.cmx vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml Fonts.cmx vfide.cmx
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o vfideredux.exe -I +lablgtk2 record_backtrace.cmx lablgtk.cmxa lablgtksourceview2.cmxa libgtksourceview-2.0-0.lib gtkInit.cmx unix.cmxa Printexc_proxy.cmx proverapi.cmx nums.cmxa simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml Fonts.cmx vfide.cmx -cclib "-L "$(GTKLIB)

win\Perf.cmxa: win\caml_perf.c win\Perf.mli win\Perf.ml win\Stopwatch.mli win\caml_stopwatch.c
	cd win
	ocamlopt.opt -a -o Perf.cmxa caml_perf.c Perf.mli Perf.ml Stopwatch.mli caml_stopwatch.c
	cd ..

DynType.mli: ..\examples\plugin\DynType.mli
	copy /B/Y generated_file_warning.txt+..\examples\plugin\DynType.mli DynType.mli

DynType.cmx: DynType.mli DynType.ml
	ocamlopt.opt -c DynType.mli DynType.ml

plugins.mli: ..\examples\plugin\plugins.mli
	copy /B/Y generated_file_warning.txt+..\examples\plugin\plugins.mli plugins.mli

plugins.cmi: DynType.cmx plugins.mli
	ocamlopt.opt -c plugins.mli

plugins.cmx: plugins.cmi plugins.ml
	ocamlopt.opt -c plugins.ml

plugins_private.cmx: plugins.cmi plugins_private.ml
	ocamlopt.opt -c plugins_private.ml

plugins2.mli: ..\examples\plugin\plugins2.mli
	copy /B/Y generated_file_warning.txt+..\examples\plugin\plugins2.mli plugins2.mli

plugins2.cmi: plugins2.mli
	ocamlopt.opt -c plugins2.mli

plugins2.cmx: plugins.cmi plugins_private.cmx plugins2.cmi
	ocamlopt.opt -c plugins2.ml

trivial_verifast_plugin.cmxs: DynType.cmx plugins.cmi plugins2.cmi trivial_plugin.ml
	ocamlopt.opt -o trivial_verifast_plugin.cmxs -shared DynType.cmx trivial_plugin.ml

#verifast.cmx: pa_verifast.cmo win\Perf.cmxa vfversion.cmi proverapi.cmx plugins.cmx verifast.ml
#	time < nl.txt
#	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -pp "camlp4o pa_verifast.cmo" -c -I .\win Perf.cmxa proverapi.cmx verifast.ml
#	time < nl.txt

util.cmx: pa_verifast.cmo win\Perf.cmxa vfversion.cmi proverapi.cmx plugins2.cmx util.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win util.ml
	time < nl.txt

stats.cmx: util.cmx stats.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win stats.ml
	time < nl.txt

lexer.cmx: stats.cmx lexer.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win lexer.ml
	time < nl.txt

ast.cmx: lexer.cmx ast.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win ast.ml
	time < nl.txt

parser.cmx: ast.cmx parser.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -pp camlp4o -c -I .\win parser.ml
	time < nl.txt

verifast0.cmx: parser.cmx verifast0.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win verifast0.ml
	time < nl.txt

verifast1.cmx: verifast0.cmx verifast1.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win verifast1.ml
	time < nl.txt

assertions.cmx: verifast1.cmx assertions.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win assertions.ml
	time < nl.txt

verify_expr.cmx: assertions.cmx verify_expr.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win verify_expr.ml
	time < nl.txt

verifast.cmx: verify_expr.cmx verifast.ml
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error FSU -c -I .\win verifast.ml
	time < nl.txt

verifast.cmo: vfversion.cmi proverapi.cmo verifast.ml
	time < nl.txt
	ocamlc.opt -warn-error F -w p -g -pp camlp4o -c verifast.ml
	time < nl.txt

simplex.cmo: simplex.ml
	ocamlc -warn-error F -g -c simplex.ml

proverapi.cmo: proverapi.ml
	ocamlc -warn-error F -g -c proverapi.ml

redux.cmo: proverapi.cmo simplex.cmo redux.ml
	ocamlc -warn-error F -w p -g -c redux.ml

z3prover.cmo: proverapi.cmo z3prover.ml
	ocamlc -warn-error F -g -c -I $(Z3)\ocaml z3prover.ml

verifastz3redux_opt.exe: record_backtrace.cmx vfversion_cmx proverapi.cmx redux.cmx z3prover.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o verifastz3redux_opt.exe -I $(Z3)\ocaml record_backtrace.cmx ole32.lib $(OCAMLLIB)\libcamlidl.lib unix.cmxa z3.cmxa proverapi.cmx redux.cmx z3prover.cmx vfversion.cmx verifast.ml verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml

..\bin\verifast.exe: tabhunt record_backtrace.cmx vfversion_cmx proverapi.cmx z3prover.cmx simplex.cmx redux.cmx DynType.cmx plugins.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx verifastPluginZ3.ml verifastPluginRedux.ml vfconsole.ml sexpressions.cmx SExpressionEmitter.cmx
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o ..\bin\verifast.exe -I $(Z3)\ocaml -I .\win record_backtrace.cmx unix.cmxa nums.cmxa z3.cmxa Perf.cmxa proverapi.cmx z3prover.cmx simplex.cmx redux.cmx vfversion.cmx Dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx plugins2.cmx util.cmx stats.cmx lexer.cmx ast.cmx parser.cmx verifast0.cmx verifast1.cmx assertions.cmx verify_expr.cmx verifast.cmx sexpressions.cmx SExpressionEmitter.cmx verifastPluginRedux.ml verifastPluginZ3.ml vfconsole.ml
	time < nl.txt

..\bin\verifastz3v2.exe: tabhunt record_backtrace.cmx vfversion_cmx proverapi.cmx z3v2prover.cmx simplex.cmx redux.cmx DynType.cmx plugins.cmx plugins2.cmx verifast.cmx verifastPluginZ3v2.ml verifastPluginRedux.ml vfconsole.ml sexpressions.cmx SExpressionEmitter.cmx
	time < nl.txt
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o ..\bin\verifastz3v2.exe -I $(Z3V2)\ocaml -I .\win record_backtrace.cmx unix.cmxa nums.cmxa z3.cmxa Perf.cmxa proverapi.cmx z3v2prover.cmx simplex.cmx redux.cmx vfversion.cmx Dynlink.cmxa DynType.cmx plugins.cmx plugins_private.cmx plugins2.cmx verifast.cmx sexpressions.cmx SExpressionEmitter.cmx verifastPluginRedux.ml verifastPluginZ3v2.ml vfconsole.ml
	time < nl.txt

proverapi.cmx: proverapi.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c proverapi.ml

simplex.cmi: simplex.mli
	ocamlopt.opt -c simplex.mli

simplex.cmx: win\Perf.cmxa simplex.cmi simplex.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I .\win Perf.cmxa simplex.ml

redux.cmx: win\Perf.cmxa proverapi.cmx simplex.cmx redux.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I .\win Perf.cmxa redux.ml

z3prover.cmx: win\Perf.cmxa proverapi.cmx z3prover.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I $(Z3)\ocaml z3.cmxa -I .\win Perf.cmxa proverapi.cmx z3prover.ml
    
z3v2prover.cmx: win\Perf.cmxa proverapi.cmx z3v2prover.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c -I $(Z3V2)\ocaml z3.cmxa -I .\win Perf.cmxa proverapi.cmx z3v2prover.ml

verifastredux_opt.exe: record_backtrace.cmx vfversion_cmx proverapi.cmx simplex.cmx redux.cmx verifast.cmx verifastPluginRedux.ml vfconsole.ml
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -pp camlp4o -o verifastRedux_opt.exe record_backtrace.cmx unix.cmxa nums.cmxa proverapi.cmx simplex.cmx redux.cmx vfversion.cmx verifast.cmx verifastPluginRedux.ml vfconsole.ml

SExpressions.cmi: verifast.cmx SExpressions.mli
	ocamlopt.opt -warn-error F -c SExpressions.mli

SExpressions.cmo: verifast.cmo SExpressions.ml SExpressions.cmi
	ocamlc -warn-error F -c nums.cma SExpressions.ml

SExpressions.cmx: verifast.cmx SExpressions.ml SExpressions.cmi
	ocamlopt.opt $(OPT_OPTIONS) -warn-error F -c nums.cmxa SExpressions.ml

SExpressionEmitter.cmi: verifast.cmx SExpressionEmitter.mli
	ocamlc -warn-error F -c SExpressionEmitter.mli

SExpressionEmitter.cmo: SExpressions.cmo verifast.cmo SExpressionEmitter.ml SExpressionEmitter.cmi
	ocamlc -w p -warn-error F -c nums.cma SExpressions.cmo verifast.cmo SExpressionEmitter.ml

SExpressionEmitter.cmx: SExpressions.cmx verifast.cmx SExpressionEmitter.ml SExpressionEmitter.cmi
	ocamlopt.opt $(OPT_OPTIONS) -w p -warn-error F -c nums.cmxa SExpressions.cmx verifast.cmx SExpressionEmitter.ml

# For testing purposes, ignore this
fred: ..\bin\verifast.exe
#	-verifast -shared -emit_sexpr_fail test.lisp test.c
#	-verifast -shared -emit_sexpr_fail test2.lisp test2.c
#	-verifast -shared -emit_sexpr_fail test3.lisp test3.c
	-verifast -disable_overflow_check -shared -stats shape-full.c shape-precise.c shape-precise-auto.c shape-none.c | ruby readstats.rb
#	verifast -disable_overflow_check -shared -stats shape-precise.c
#	verifast -disable_overflow_check -shared -stats shape-precise-auto.c
	@-verifast -shared -stats -emit_sexpr_fail shape-none.lisp shape-none.c > ignore.txt  # - indicates we do not expect successful verification (i.e. ignore error codes)
	@copy shape-* $(SHAPEANALYSIS)\src\vf > ignore.txt
	@copy *.lisp $(SHAPEANALYSIS)\src\vf > ignore.txt

fred2: ..\bin\verifast.exe
	verifast -c -shared -emit_highlighted_source_files test3.c

# Builds necessary files for REPL-use (needed due to .cmo files not being necessary for verifast.exe)
repl: cmo ..\bin\verifast.exe


release: test refman
	-rmdir /s verifast-$(VFVERSION)
	mkdir verifast-$(VFVERSION)
	cd verifast-$(VFVERSION)
	copy $(Z3)\LICENSE.txt z3.LICENSE.txt
	xcopy /E /I ..\..\bin bin
	cd bin
	copy $(GTKLIB)\..\bin\freetype6.dll
	copy $(GTKLIB)\..\bin\iconv.dll
	copy $(GTKLIB)\..\bin\intl.dll
	copy $(GTKLIB)\..\bin\libatk-1.0-0.dll
	copy $(GTKLIB)\..\bin\libcairo-2.dll
	copy $(GTKLIB)\..\bin\libexpat-1.dll
	copy $(GTKLIB)\..\bin\libfontconfig-1.dll
	copy $(GTKLIB)\..\bin\libgdk-win32-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgdk_pixbuf-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgio-2.0-0.dll
	copy $(GTKLIB)\..\bin\libglib-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgmodule-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgobject-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgthread-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgtk-win32-2.0-0.dll
	copy $(GTKLIB)\..\bin\libgtksourceview-2.0-0.dll
	copy $(GTKLIB)\..\bin\libpango-1.0-0.dll
	copy $(GTKLIB)\..\bin\libpangocairo-1.0-0.dll
	copy $(GTKLIB)\..\bin\libpangoft2-1.0-0.dll
	copy $(GTKLIB)\..\bin\libpangowin32-1.0-0.dll
	copy $(GTKLIB)\..\bin\libpng14-14.dll
	copy $(GTKLIB)\..\bin\libxml2-2.dll
	copy $(GTKLIB)\..\bin\zlib1.dll
	copy $(Z3)\bin\z3.dll
	xcopy /E $(Z3)\bin\Microsoft.VC90.CRT .
	copy "$(MSVC10REDIST)\MSVCR100.DLL"
	cd ..
	mkdir etc
	cd etc
	mkdir gtk-2.0
	cd gtk-2.0
	echo > gdk-pixbuf.loaders
	echo gtk-theme-name = "MS-Windows" > gtkrc
	cd ..
	cd ..
	mkdir share\themes\MS-Windows\gtk-2.0
	cd share\themes\MS-Windows\gtk-2.0
	copy $(GTKLIB)\..\share\themes\MS-Windows\gtk-2.0\gtkrc
	cd ..\..\..\..
	mkdir lib\gtk-2.0\2.10.0\engines
	copy $(GTKLIB)\gtk-2.0\2.10.0\engines\libwimp.dll lib\gtk-2.0\2.10.0\engines
	mkdir doc
	cd doc
	copy ..\..\..\doc\refman\refman.pdf
	cd ..
	xcopy /E /I ..\..\examples examples
	xcopy /E /I ..\..\tests tests
	xcopy /E /I ..\..\tutorial_solutions tutorial_solutions
	xcopy /E /I ..\..\help help
	xcopy /E /I ..\..\javacard_tutorial javacard_tutorial
	mkdir tutorial
	cd tutorial_solutions
	for %f in (*.c) do vfstrip < %f > ..\tutorial\%f
	cd ..
	copy ..\..\testsuite.mysh
	copy ..\..\test.bat
