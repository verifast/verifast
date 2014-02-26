# This makefile builds the *dependencies* of VeriFast like ocaml, and calls
# the makefile in src/ that builds verifast itself. If the makefile
# you currently are looking at does not work, you can install the dependencies
# by hand and use src/GNUmakefile to build VeriFast.

# --- Config  ---------------------------------------------------------------

#Z3v1     = true
#Z3v4     = true
#noZ3     = true
  
# --- End of Config  --------------------------------------------------------


OCAMLSRC = ocaml-4.00.1
OCAMLURL = http://caml.inria.fr/pub/distrib/ocaml-4.00/
OCAMLPKG = ${OCAMLSRC}.tar.gz
OCAMLDIR = $(shell pwd)/${OCAMLSRC}

CIDLSRC  = camlidl-1.05
CIDLURL  = http://caml.inria.fr/pub/old_caml_site/distrib/bazar-ocaml/
CIDLPKG  = ${CIDLSRC}.tar.gz

LGTKSRC  = lablgtk-2.14.2
LGTKURL  = http://wwwfun.kurims.kyoto-u.ac.jp/soft/lsl/dist/
LGTKPKG  = ${LGTKSRC}.tar.gz

ifdef Z3v1
  Z3SRC  = z3
  Z3URL  = https://dnetcode.cs.kuleuven.be/attachments/download/736/
  Z3PKG  = z3.tar.gz
else ifdef Z3v4
  Z3SRC  = z3v4
  Z3URL  = https://dnetcode.cs.kuleuven.be/attachments/download/736/
  Z3PKG  = z3-4.3.1.tar.gz
else ifdef noZ3
  Z3SRC  =
  Z3URL  =
  Z3PKG  =
else
  $(error Neither Z3v1, Z3v4, nor noZ3 is defined. \
    Use "make <Z3v1|Z3v4|noZ3>=true" to compile. Support Z3v4 \
    is experimental and should not be used)
endif

LASTZ3   = $(shell cat lastz3)

all: ocaml cidl lgtk
	$(MAKE) GNUmakefile.settings
ifdef Z3v1
  ifneq ($(LASTZ3),Z3v1)
	rm -f z3build
	$(MAKE) -C src -f GNUmakefile clean
  endif
	echo "Z3v1" >lastz3
else ifdef Z3v4
  ifneq ($(LASTZ3),Z3v4)
	rm -f z3build
	$(MAKE) -C src -f GNUmakefile clean
  endif
	echo "Z3v4" >lastz3
else ifdef noZ3
  ifneq ($(LASTZ3),noZ3)
	rm -f z3build
	$(MAKE) -C src -f GNUmakefile clean
  endif
	echo "noZ3" >lastz3
endif
	rm -f GNUmakefile.settings
	$(MAKE) GNUmakefile.settings
	$(MAKE) z3build
	$(MAKE) -C src -f GNUmakefile all VERBOSE=1

rebuild:
	$(MAKE) -C src -f GNUmakefile build

ocaml: GNUmakefile
	rm -rf ${OCAMLPKG} ${OCAMLDIR} ${OCAMLSRC}
	wget ${OCAMLURL}${OCAMLPKG}
	gunzip -c ${OCAMLPKG} | tar -xv
	cd ${OCAMLSRC}; ./configure -prefix ${OCAMLDIR} -ccoption "gcc -m32" \
          -as "as --32" -aspp "gcc -m32 -c" -host i386-linux \
          -partialld "ld -r -melf_i386"
	cd ${OCAMLSRC}; ${MAKE} world
	cd ${OCAMLSRC}; ${MAKE} opt
	cd ${OCAMLSRC}; ${MAKE} install
	cd ${OCAMLSRC}; ${MAKE} clean
	echo ${OCAMLDIR} >ocaml

cidl: GNUmakefile ocaml
	rm -rf ${CIDLPKG} ${CIDLSRC}
	wget ${CIDLURL}${CIDLPKG}
	gunzip -c ${CIDLPKG} | tar -xv
	sed 's#/usr/local#${OCAMLDIR}#g'\
          ${CIDLSRC}/config/Makefile.unix >${CIDLSRC}/config/Makefile
	cd ${CIDLSRC}; export PATH=${OCAMLDIR}/bin:$$PATH; ${MAKE} all
	cd ${CIDLSRC}; export PATH=${OCAMLDIR}/bin:$$PATH; ${MAKE} install
	cd ${CIDLSRC}; export PATH=${OCAMLDIR}/bin:$$PATH; ${MAKE} clean
	touch cidl

lgtk: GNUmakefile ocaml
	rm -rf ${LGTKPKG} ${LGTKSRC}
	wget ${LGTKURL}${LGTKPKG}
	gunzip -c ${LGTKPKG} | tar -xv
	cd ${LGTKSRC}; export PATH=${OCAMLDIR}/bin:$$PATH; \
          ./configure --prefix=${OCAMLDIR} CC="gcc -m32"
	grep "USE_GTKSOURCEVIEW2='1'" ${LGTKSRC}/config.log; \
          echo "$$?" >lgtk.conf
	if [ `cat lgtk.conf` -eq 0 ]; then \
          cd ${LGTKSRC}; export PATH=${OCAMLDIR}/bin:$$PATH; \
          ${MAKE} all install && \
          ${MAKE} -C src gtkInit.cmx gtkInit.o lablgtksourceview2.cmxa \
            lablgtksourceview2.a lablgtk.cmxa lablgtk.a && \
          cp src/gtkInit.cmx src/gtkInit.o \
            src/lablgtksourceview2.cmxa src/lablgtksourceview2.a \
            src/lablgtk.cmxa src/lablgtk.a ${OCAMLDIR}/lib/ocaml/lablgtk2/ && \
          cd ../ && \
          echo "0" >lgtk; \
         else \
          echo "*** GTKSOURCEVIEW not installed. VFIDE will not be built."; \
          echo "1" >lgtk; \
         fi

z3build: GNUmakefile ocaml cidl
ifdef Z3v1
	rm -rf ${Z3SRC}
	@echo Download ${Z3URL}${Z3PKG}
	@echo to this directory and press return.
	@bash -c read
	gunzip -c ${Z3PKG} | tar -xv
	cd ${Z3SRC}/ocaml; export PATH=${OCAMLDIR}/bin:$$PATH; \
          ./build-lib.sh `ocamlc -where`
	echo $(shell pwd)/${Z3SRC} >z3build
else ifdef Z3v4
	rm -rf ${Z3SRC}
	@echo Download ${Z3URL}${Z3PKG}
	@echo to this directory and press return.
	@bash -c read
	gunzip -c ${Z3PKG} | tar -xv
	cd ${Z3SRC}; export PATH=${OCAMLDIR}/bin:$$PATH; \
          autoconf && ./configure --prefix=$(shell pwd)/${Z3SRC} && \
          python scripts/mk_make.py && cd build; make
	cd ${Z3SRC}/build; export PATH=${OCAMLDIR}/bin:$$PATH; make install; \
          true  # "install" always fails -- TODO
	cd ${Z3SRC}; cp -r src/api/ml/ ./ocaml
	cp build_helpers/z3v4/Makefile.z3v4.ocaml ${Z3SRC}/ocaml/Makefile
	cp build_helpers/z3v4/z3_stubs.c ${Z3SRC}/ocaml/
	cd ${Z3SRC}/ocaml; chmod a+x build-lib.sh && \
          export PATH=${OCAMLDIR}/bin:$$PATH; \
          export LD_LIBRARY_PATH=${Z3SRC}/lib:$$LD_LIBRARY_PATH; \
          ${MAKE}
	echo $(shell pwd)/${Z3SRC} >z3build
else ifdef noZ3
	touch z3build
else
	$(error Neither Z3v1, Z3v4, nor noZ3 is defined for \
          target z3build)
endif

GNUmakefile.settings: GNUmakefile.settings.local lgtk
ifdef Z3v1
	cat GNUmakefile.settings.local | \
          sed 's/^#Z3 /Z3 /g;s/^NOZ3 /#NOZ3 /;' > GNUmakefile.settings
else ifdef Z3v4
	cat GNUmakefile.settings.local | \
          sed 's/^#Z3V4 /Z3V4 /g;s/^NOZ3 /#NOZ3 /;' > GNUmakefile.settings
else ifdef noZ3
	cp GNUmakefile.settings.local GNUmakefile.settings
else
	$(error Neither Z3v1, Z3v4, nor noZ3 is defined for \
          target GNUmakefile.settings)
endif
	if [ `cat lgtk` -eq 1 ]; then \
          echo "WITHOUT_LABLGTK = yes" >>GNUmakefile.settings; \
        fi

touch:
	touch ocaml cidl lgtk z3build

clean:
	rm -f test
	$(MAKE) -C src -f GNUmakefile clean

distclean: clean
	rm -rf ${OCAMLPKG} ${OCAMLDIR} ${OCAMLSRC} ocaml
	rm -rf ${CIDLPKG} ${CIDLSRC} cidl
	rm -rf ${LGTKPKG} ${LGTKSRC} lgtk
	rm -rf ${Z3SRC} z3build lastz3

