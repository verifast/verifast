PREFIX=C:/vfdeps-17.12
MAKEDIR:=$(shell pwd)
PATH:=$(shell cygpath "$(MAKEDIR)"):$(shell cygpath "$(PREFIX)")/bin:$(PATH)

all: ocaml findlib num ocamlbuild camlp4 gtk lablgtk z3

clean::
	-rm -Rf $(PREFIX)

# ---- OCaml ----

OCAML_VERSION=4.06.0
OCAML_TGZ=ocaml-$(OCAML_VERSION).tar.gz
OCAML_SRC=ocaml-$(OCAML_VERSION)/config/Makefile.mingw
FLEXDLL_VERSION=0.37
FLEXDLL_TGZ=flexdll-$(FLEXDLL_VERSION).tar.gz
FLEXDLL_SRC=flexdll-$(FLEXDLL_VERSION)/flexdll.c
OCAML_EXE=$(PREFIX)/bin/ocamlopt.opt.exe

$(OCAML_TGZ):
	curl -Lfo ocaml-$(OCAML_VERSION).tar.gz https://github.com/ocaml/ocaml/archive/$(OCAML_VERSION).tar.gz

$(OCAML_SRC): $(OCAML_TGZ)
	tar xzfm $(OCAML_TGZ)

$(FLEXDLL_TGZ):
	curl -Lfo $(FLEXDLL_TGZ) https://github.com/alainfrisch/flexdll/archive/$(FLEXDLL_VERSION).tar.gz

$(FLEXDLL_SRC): $(FLEXDLL_TGZ)
	tar xzfm $(FLEXDLL_TGZ)

ocaml-$(OCAML_VERSION)/flexdll/flexdll.c: $(OCAML_SRC) $(FLEXDLL_SRC)
	cd ocaml-$(OCAML_VERSION)/flexdll && cp -R ../../flexdll-$(FLEXDLL_VERSION)/* .

ocaml-$(OCAML_VERSION)/config/Makefile: $(OCAML_SRC)
	cd ocaml-$(OCAML_VERSION) && \
		cp config/m-nt.h byterun/caml/m.h && \
		cp config/s-nt.h byterun/caml/s.h && \
		cp config/Makefile.mingw config/Makefile && \
		patch config/Makefile ../ocaml-Makefile.patch

$(OCAML_EXE): ocaml-$(OCAML_VERSION)/config/Makefile ocaml-$(OCAML_VERSION)/flexdll/flexdll.c
	cd ocaml-$(OCAML_VERSION) && \
		make flexdll world opt opt.opt flexlink.opt install

ocaml: $(OCAML_EXE)
.PHONY: ocaml

clean::
	-rm -Rf ocaml-$(OCAML_VERSION)
	-rm -Rf flexdll-$(FLEXDLL_VERSION)

# ---- Findlib ----

FINDLIB_VERSION=1.7.3
FINDLIB_EXE=$(PREFIX)/bin/ocamlfind.exe
FINDLIB_TGZ=findlib-$(FINDLIB_VERSION).tar.gz
FINDLIB_SRC=findlib-$(FINDLIB_VERSION)/configure
FINDLIB_CFG=findlib-$(FINDLIB_VERSION)/Makefile.config

$(FINDLIB_TGZ):
	curl -Lfo $(FINDLIB_TGZ) http://download.camlcity.org/download/findlib-$(FINDLIB_VERSION).tar.gz

$(FINDLIB_SRC): $(FINDLIB_TGZ)
	tar xzfm $(FINDLIB_TGZ)

$(FINDLIB_CFG): $(OCAML_EXE) $(FINDLIB_SRC)
	cd findlib-$(FINDLIB_VERSION) && \
	./configure \
	  -bindir $(PREFIX)/bin \
	  -mandir $(PREFIX)/man \
	  -sitelib $(PREFIX)/lib/ocaml \
	  -config $(PREFIX)/etc/findlib.conf

$(FINDLIB_EXE): $(FINDLIB_CFG)
	cd findlib-$(FINDLIB_VERSION) && \
	make all && \
	make opt && \
	make install

findlib: $(FINDLIB_EXE)
.PHONY: findlib

clean::
	-rm -Rf findlib-$(FINDLIB_VERSION)

# ---- Num ----

NUM_VERSION=1.1
NUM_BINARY=$(PREFIX)/lib/ocaml/nums.cmxa
NUM_TGZ=num-$(NUM_VERSION).tar.gz
NUM_SRC=num-$(NUM_VERSION)/Makefile

$(NUM_TGZ):
	curl -Lfo $(NUM_TGZ) https://github.com/ocaml/num/archive/v$(NUM_VERSION).tar.gz

$(NUM_SRC): $(NUM_TGZ)
	tar xzfm $(NUM_TGZ)

$(NUM_BINARY): $(NUM_SRC) $(FINDLIB_EXE)
	cd num-$(NUM_VERSION) && make && make install SO=dll

num: $(NUM_BINARY)
.PHONY: num

clean::
	-rm -Rf num-$(NUM_VERSION)

# ---- ocamlbuild ----

OCAMLBUILD_VERSION=0.12.0
OCAMLBUILD_BINARY=$(PREFIX)/bin/ocamlbuild.exe
OCAMLBUILD_TGZ=ocamlbuild-$(OCAMLBUILD_VERSION).tar.gz
OCAMLBUILD_SRC=ocamlbuild-$(OCAMLBUILD_VERSION)/Makefile

$(OCAMLBUILD_TGZ):
	curl -Lfo $(OCAMLBUILD_TGZ) https://github.com/ocaml/ocamlbuild/archive/$(OCAMLBUILD_VERSION).tar.gz

$(OCAMLBUILD_SRC): $(OCAMLBUILD_TGZ)
	tar xzfm $(OCAMLBUILD_TGZ)

$(OCAMLBUILD_BINARY): $(FINDLIB_BINARY) $(OCAMLBUILD_SRC)
	cd ocamlbuild-$(OCAMLBUILD_VERSION) && \
	make configure && make && make install

ocamlbuild: $(OCAMLBUILD_BINARY)
.PHONY: ocamlbuild

clean::
	-rm -Rf ocamlbuild-$(OCAMLBUILD_VERSION)

# ---- camlp4 ----

CAMLP4_VERSION=4.06+1
CAMLP4_DIR=camlp4-$(subst +,-,$(CAMLP4_VERSION))
CAMLP4_BINARY=$(PREFIX)/bin/camlp4o.exe
CAMLP4_TGZ=camlp4-$(CAMLP4_VERSION).tar.gz
CAMLP4_SRC=$(CAMLP4_DIR)/configure

$(CAMLP4_TGZ):
	curl -Lfo $(CAMLP4_TGZ) https://github.com/ocaml/camlp4/archive/$(CAMLP4_VERSION).tar.gz

$(CAMLP4_SRC): $(CAMLP4_TGZ)
	tar xzfm $(CAMLP4_TGZ)

$(CAMLP4_BINARY): $(OCAMLBUILD_BINARY) $(CAMLP4_SRC)
	cd $(CAMLP4_DIR) && \
	./configure && make all && make install

camlp4: $(CAMLP4_BINARY)
.PHONY: camlp4

clean::
	-rm -Rf $(CAMLP4_DIR)

# ---- GTK ----

GTK_BINARY=$(PREFIX)/bin/gtk-demo.exe

$(GTK_BINARY):
	cd $(PREFIX) && \
	  for url in \
	    ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtk+/2.24/gtk+-bundle_2.24.10-20120208_win32.zip \
	    ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-2.10.0.zip \
	    ftp://ftp.gnome.org/pub/gnome/binaries/win32/gtksourceview/2.10/gtksourceview-dev-2.10.0.zip \
	    ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2_2.9.0-1_win32.zip \
	    ftp://ftp.gnome.org/pub/gnome/binaries/win32/dependencies/libxml2-dev_2.9.0-1_win32.zip \
	  ; do \
	    download_and_unzip --dlcache "$(MAKEDIR)" "$$url" \
	  ; done && \
	  mv bin/pkg-config.exe bin/pkg-config.exe_ && \
	  cp "$(MAKEDIR)/pkg-config" bin && \
	  mv bin/pkg-config.exe_ bin/pkg-config.exe

gtk: $(GTK_BINARY)
.PHONY: gtk

# ---- lablgtk ----

LABLGTK_VERSION=2.18.6
LABLGTK_SRC=lablgtk-$(LABLGTK_VERSION)/configure
LABLGTK_CFG=lablgtk-$(LABLGTK_VERSION)/config.make
LABLGTK_BUILD=lablgtk-$(LABLGTK_VERSION)/src/lablgtk2.cmxa
LABLGTK_BINARY=$(PREFIX)/lib/ocaml/lablgtk2/lablgtk2.cmxa

$(LABLGTK_SRC):
	download_and_untar https://forge.ocamlcore.org/frs/download.php/1726/lablgtk-$(LABLGTK_VERSION).tar.gz

$(LABLGTK_CFG): $(LABLGTK_SRC) $(CAMLP4_BINARY) $(GTK_BINARY)
	cd lablgtk-$(LABLGTK_VERSION) && \
	  ./configure

$(LABLGTK_BUILD): $(LABLGTK_CFG)
	cd lablgtk-$(LABLGTK_VERSION) && \
	  make && make opt

$(LABLGTK_BINARY): $(LABLGTK_BUILD)
	cd lablgtk-$(LABLGTK_VERSION) && make install

lablgtk: $(LABLGTK_BINARY)
.PHONY: lablgtk

clean::
	-rm -Rf lablgtk-$(LABLGTK_VERSION)

# ---- Z3 ----

Z3_VERSION=4.5.0
Z3_BINARY=$(PREFIX)/lib/libz3.dll
Z3_DIR=z3-z3-$(Z3_VERSION)
Z3_SRC=$(Z3_DIR)/scripts/mk_make.py
Z3_CFG=$(Z3_DIR)/build/Makefile
Z3_BUILD=$(Z3_DIR)/build/libz3.dll

$(Z3_SRC):
	download_and_untar https://github.com/Z3Prover/z3/archive/z3-$(Z3_VERSION).tar.gz

$(Z3_CFG): $(FINDLIB_EXE) $(Z3_SRC)
	cd $(Z3_DIR) && CXX=i686-w64-mingw32-g++ CC=i686-w64-mingw32-gcc AR=i686-w64-mingw32-ar python scripts/mk_make.py --ml --prefix=$(PREFIX)

$(Z3_BUILD): $(Z3_CFG)
	cd $(Z3_DIR)/build && make

$(Z3_BINARY): $(Z3_BUILD)
	cd $(Z3_DIR)/build && make install && cp build/libz3.dll.a $(PREFIX)/lib

z3: $(Z3_BINARY)
.PHONY: z3

clean::
	-rm -Rf $(Z3_DIR)
