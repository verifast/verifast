
OCAMLSRC = ocaml-3.12.1
OCAMLURL = http://caml.inria.fr/pub/distrib/ocaml-3.12/
OCAMLPKG = ${OCAMLSRC}.tar.gz
OCAMLDIR = $(shell pwd)/ocaml-3.12.1

CIDLSRC  = camlidl-1.05
CIDLURL  = http://caml.inria.fr/pub/old_caml_site/distrib/bazar-ocaml/
CIDLPKG  = ${CIDLSRC}.tar.gz

LGTKSRC  = lablgtk-2.14.2
LGTKURL  = http://wwwfun.kurims.kyoto-u.ac.jp/soft/lsl/dist/
LGTKPKG  = ${LGTKSRC}.tar.gz

Z3SRC    = z3
Z3URL    = https://dnetcode.cs.kuleuven.be/attachments/download/679/
Z3PKG    = z3.tar.gz
#Z3PKG    = z3-4.0.tar.gz


all: ocaml cidl lgtk z3build GNUmakefile.settings
	$(MAKE) -C src -f GNUmakefile all

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
          ./configure --prefix=${OCAMLDIR} CC="gcc -m32"; \
          echo "$$?" >lgtk.conf
	if [ `cat ${LGTKSRC}/lgtk.conf` -eq 0 ]; then \
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
          echo "1" >lgtk; \
         fi

z3build: GNUmakefile ocaml
	rm -rf ${Z3SRC}
	@echo Download ${Z3URL}${Z3PKG}
	@echo to this directory and press return.
	@bash -c read
	gunzip -c ${Z3PKG} | tar -xv
	cd ${Z3SRC}/ocaml; export PATH=${OCAMLDIR}/bin:$$PATH; \
          ./build-lib.sh `ocamlc -where`
	echo $(shell pwd)/${Z3SRC} >z3build

GNUmakefile.settings: GNUmakefile.settings.local lgtk
	cp GNUmakefile.settings.local GNUmakefile.settings
	if [ `cat lgtk` -eq 1 ]; then \
          echo "WITHOUT_LABLGTK = yes" >>GNUmakefile.settings; \
        fi

clean:
	rm -f test
	$(MAKE) -C src -f GNUmakefile clean

distclean: clean
	rm -rf ${OCAMLPKG} ${OCAMLDIR} ${OCAMLSRC} ocaml
	rm -rf ${CIDLPKG} ${CIDLSRC} cidl
	rm -rf ${LGTKPKG} ${LGTKSRC} lgtk
	rm -rf ${Z3SRC} z3build

