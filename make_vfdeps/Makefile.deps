PATH:=$(PREFIX)/bin:$(PATH)

all: ocaml findlib num ocamlbuild camlp4 lablgtk z3

# ---- OCaml ----

OCAML_VERSION=4.06.0
OCAML_BINARY=$(PREFIX)/bin/ocamlopt.opt

ocaml-$(OCAML_VERSION).tar.gz:
	curl -L https://github.com/ocaml/ocaml/archive/$(OCAML_VERSION).tar.gz > ocaml-$(OCAML_VERSION).tar.gz

ocaml-$(OCAML_VERSION): ocaml-$(OCAML_VERSION).tar.gz
	tar xzf ocaml-$(OCAML_VERSION).tar.gz

$(OCAML_BINARY): | ocaml-$(OCAML_VERSION)
	cd ocaml-$(OCAML_VERSION) && \
        ./configure -prefix $(PREFIX) && \
        make world.opt && \
        make install

ocaml: $(OCAML_BINARY)
.PHONY: ocaml

clean::
	-rm -Rf ocaml-$(OCAML_VERSION)

# ---- Findlib ----

FINDLIB_VERSION=1.7.3
FINDLIB_BINARY=$(PREFIX)/bin/ocamlfind

findlib-$(FINDLIB_VERSION).tar.gz:
	curl -L http://download.camlcity.org/download/findlib-$(FINDLIB_VERSION).tar.gz > findlib-$(FINDLIB_VERSION).tar.gz

findlib-$(FINDLIB_VERSION): findlib-$(FINDLIB_VERSION).tar.gz
	tar xzf findlib-$(FINDLIB_VERSION).tar.gz

findlib-$(FINDLIB_VERSION)/Makefile.config: $(OCAML_BINARY) | findlib-$(FINDLIB_VERSION)
	cd findlib-$(FINDLIB_VERSION) && \
	./configure \
	  -bindir $(PREFIX)/bin \
          -mandir $(PREFIX)/man \
          -sitelib $(PREFIX)/lib/ocaml \
          -config $(PREFIX)/etc/findlib.conf

$(FINDLIB_BINARY): findlib-$(FINDLIB_VERSION)/Makefile.config
	cd findlib-$(FINDLIB_VERSION) && \
        make all && \
        make opt && \
        make install

findlib: $(FINDLIB_BINARY)
.PHONY: findlib

clean::
	-rm -Rf findlib-$(FINDLIB_VERSION)

# ---- Num ----

NUM_VERSION=1.1
NUM_BINARY=$(PREFIX)/lib/ocaml/nums.cmxa

num-$(NUM_VERSION).tar.gz:
	curl -Lfo num-$(NUM_VERSION).tar.gz https://github.com/ocaml/num/archive/v$(NUM_VERSION).tar.gz

num-$(NUM_VERSION): num-$(NUM_VERSION).tar.gz
	tar xzf num-$(NUM_VERSION).tar.gz

$(NUM_BINARY): $(FINDLIB_BINARY) | num-$(NUM_VERSION)
	cd num-$(NUM_VERSION) && make all && make install

num: $(NUM_BINARY)
.PHONY: num

clean::
	-rm -Rf num-$(NUM_VERSION)

# ---- ocamlbuild ----

OCAMLBUILD_VERSION=0.12.0
OCAMLBUILD_BINARY=$(PREFIX)/bin/ocamlbuild

ocamlbuild-$(OCAMLBUILD_VERSION).tar.gz:
	curl -Lfo ocamlbuild-$(OCAMLBUILD_VERSION).tar.gz https://github.com/ocaml/ocamlbuild/archive/$(OCAMLBUILD_VERSION).tar.gz

ocamlbuild-$(OCAMLBUILD_VERSION): ocamlbuild-$(OCAMLBUILD_VERSION).tar.gz
	tar xzf ocamlbuild-$(OCAMLBUILD_VERSION).tar.gz

$(OCAMLBUILD_BINARY): $(FINDLIB_BINARY) | ocamlbuild-$(OCAMLBUILD_VERSION)
	cd ocamlbuild-$(OCAMLBUILD_VERSION) && \
        make configure && make && make install

ocamlbuild: $(OCAMLBUILD_BINARY)
.PHONY: ocamlbuild

clean::
	-rm -Rf ocamlbuild-$(OCAMLBUILD_VERSION)

# ---- camlp4 ----

CAMLP4_VERSION:=4.06+1
CAMLP4_DIR:=camlp4-$(subst +,-,$(CAMLP4_VERSION))
CAMLP4_BINARY:=$(PREFIX)/bin/camlp4o

$(CAMLP4_DIR).tar.gz:
	curl -Lfo $(CAMLP4_DIR).tar.gz https://github.com/ocaml/camlp4/archive/$(CAMLP4_VERSION).tar.gz

$(CAMLP4_DIR): $(CAMLP4_DIR).tar.gz
	tar xzf $(CAMLP4_DIR).tar.gz

$(CAMLP4_BINARY): $(OCAMLBUILD_BINARY) | $(CAMLP4_DIR)
	cd $(CAMLP4_DIR) && \
        ./configure && make all && make install

camlp4: $(CAMLP4_BINARY)
.PHONY: camlp4

clean::
	-rm -Rf $(CAMLP4_DIR)

# ---- lablgtk ----

LABLGTK_VERSION=2.18.6
LABLGTK_BINARY=$(PREFIX)/lib/ocaml/lablgtk2/lablgtk2.cmxa

lablgtk-$(LABLGTK_VERSION).tar.gz:
	curl -Lfo lablgtk-$(LABLGTK_VERSION).tar.gz https://forge.ocamlcore.org/frs/download.php/1726/lablgtk-$(LABLGTK_VERSION).tar.gz

lablgtk-$(LABLGTK_VERSION): lablgtk-$(LABLGTK_VERSION).tar.gz
	tar xzf lablgtk-$(LABLGTK_VERSION).tar.gz

$(LABLGTK_BINARY): $(FINDLIB_BINARY) | lablgtk-$(LABLGTK_VERSION)
	cd lablgtk-$(LABLGTK_VERSION) && \
        ./configure --prefix=$(PREFIX) && make world && make install

lablgtk: $(LABLGTK_BINARY)
.PHONY: lablgtk

clean::
	-rm -Rf lablgtk-$(LABLGTK_VERSION)

# ---- Z3 ----

Z3_VERSION=4.8.5
Z3_BINARY=$(PREFIX)/bin/z3
Z3_DIR=z3-Z3-$(Z3_VERSION)

z3-$(Z3_VERSION).tar.gz:
	curl -Lfo z3-$(Z3_VERSION).tar.gz https://github.com/Z3Prover/z3/archive/Z3-$(Z3_VERSION).tar.gz

$(Z3_DIR): z3-$(Z3_VERSION).tar.gz
	tar xzf z3-$(Z3_VERSION).tar.gz

$(Z3_BINARY): $(FINDLIB_BINARY) | $(Z3_DIR)
	cd $(Z3_DIR) && \
        python scripts/mk_make.py --ml --prefix=$(PREFIX) && \
        cd build && make && make install

z3: $(Z3_BINARY)
.PHONY: z3

clean::
	-rm -Rf $(Z3_DIR)
