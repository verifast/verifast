#
# Entry point for when user types "make".
#
default:
help:
	@echo 'Usage: make [TARGET]... [PARAMETER]...'
	@echo 'Compiles VeriFast, vfide, mysh, etc.'
	@echo 'Does not build dependencies like ocaml or lablgtk.'
	@echo ''
	@echo 'Most important targets:'
	@echo '  verifast  : Builds console frontend'
	@echo '  vfide     : Builds lablgtk frontend'
	@echo '  test      : Launches testsuite'
	@echo '  clean     : Removes comiler output'
	@echo '  The default target launches verifast, vfide and test.'
	@echo ''
	@echo 'Parameters:'
	@echo '  DEBUG=1   : Enables debug build'
	@echo '  VERBOSE=1 : Shows more info scrolling by while building.'
	@echo '  BYTECODE=1: Compile to bytecode instead of to native code.'
	@echo '              Note: might result in a file containing also'
	@echo '                the runtime system. On e.g. Linux this will'
	@echo '                thus be an ELF file but it contains bytecode.'
	@echo '  ANNOT=1   : Enable writing .annot files. This allows you'
	@echo '                to see the inferred types, e.g. by pressing'
	@echo '                C-c C-t in Emacs.'
	@echo '  Z3=<path> : Sets path to Z3 bindings.'
	@echo '  Z3v2=<path>'
	@echo '  Z3v4=<path>'
	@echo '  NOZ3=1    : Do not include Z3 plugin.'
	@echo ''
	@echo '  You can save parameters by creating a file "settings.make"'
	@echo '  and populating it with lines like "NOZ3=1".'
	@echo '  See settings.make.example for an example.'
	@echo ''
	@echo 'Usage examples:'
	@echo '   make'
	@echo '   make verifast'
	@echo '   make verifast DEBUG=1 VERBOSE=1 Z3=/home/john/compiled/z3'
	@echo '   make test'

ifneq ($(OS),win)
  default:
	make -j 8 all
else
  # concurrent make does not seem to work in Windows.
  default: all
endif

all: verifast vfide test stdlib mysh dlsymtool main_class java_card_applet vfstrip

include verifast.make
include vfide.make
include vfcommon.make
include stdlib.make
include mysh.make
include test.make
include dlsymtool.make
include main_class.make
include java_card_applet.make
include vfstrip.make

