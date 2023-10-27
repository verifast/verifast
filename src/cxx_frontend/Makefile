# Don't run this file directly, use the one in src, which inlcudes this one.
# All targets/recipes are relative to src.

CXX_FE_DIR					= cxx_frontend
CXX_FE_STUBS_DIR			= $(CXX_FE_DIR)/stubs
CXX_FE_AST_EXPORTER_DIR		= $(CXX_FE_DIR)/ast_exporter

CAPNP_BIN			?= $(shell dirname `which capnp`)
CAPNP_INCLUDE		?= $(CAPNP_BIN)/../include
CAPNP_LIBS			?= $(CAPNP_BIN)/../lib
CAPNP_LINK_FLAGS	= -package capnp,capnp.unix


ifeq ($(OS), Windows_NT)
CAPNP_INCLUDE := $(shell cygpath -w $(CAPNP_INCLUDE))
CAPNP_LIBS := "$(shell cygpath -w $(CAPNP_LIBS))"
endif

export CAPNP_INCLUDE

# we specify rules here if we don't want the makefile in src to compile specific files

# ---- stubs ----
# we don't want the rule in the src/GNUmakefile to compile the stubs: 
# the camlp4 pp cannot parse '[@@@ocaml.warning ...]' attributes, which the stubs plugin generates
$(CXX_FE_STUBS_DIR)/stubs_ast.cmx: $(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -53-55 -I $(CXX_FE_STUBS_DIR) -package capnp $^

$(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml &:: $(CXX_FE_STUBS_DIR)/stubs_ast.capnp
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS) capnp compile -I "$(CAPNP_INCLUDE)" -o ocaml:$(CXX_FE_STUBS_DIR) $<

# ---- translator ----
CXX_TRANSL_DEPS = $(CXX_FE_STUBS_DIR)/stubs_ast.cmx $(CXX_FE_DIR)/cxx_annotation_parser.cmx $(CXX_FE_DIR)/cxx_ast_translator.ml $(CXX_FE_DIR)/cxx_ast_translator.ml

$(CXX_FE_DIR)/cxx_ast_translator.cmx: $(CXX_TRANSL_DEPS)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 -I $(CXX_FE_STUBS_DIR) -I $(CXX_FE_DIR) -I $(CXX_FE_DIR) -package num $(CAPNP_LINK_FLAGS) $^

CXX_FE_DEPS = $(CXX_FE_STUBS_DIR)/stubs_ast.cmx $(CXX_FE_DIR)/cxx_annotation_parser.cmx $(CXX_FE_DIR)/cxx_fe_sig.cmx $(CXX_FE_DIR)/cxx_ast_translator.cmx

# ---- ast-exporter ----
$(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++ &:: $(CXX_FE_STUBS_DIR)/stubs_ast.capnp
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS) capnp compile -I "$(CAPNP_INCLUDE)" -o c++ $<

../bin/libstdc++-6.dll: /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libstdc++-6.dll
	cp -f $< $@

ifeq ($(OS), Windows_NT)
../bin/vf-cxx-ast-exporter$(DOTEXE): ../bin/libstdc++-6.dll
endif
../bin/vf-cxx-ast-exporter$(DOTEXE): $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++ $(CXX_FE_AST_EXPORTER_DIR)/*.h $(CXX_FE_AST_EXPORTER_DIR)/*.cpp
	@echo "  MAKE " $@
	cd $(CXX_FE_AST_EXPORTER_DIR) && cmake --build build
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && mv vf-cxx-ast-exporter$(DOTEXE) ../../../$@

stubs: $(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++
.PHONY: stubs

clean::
	rm -f $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.*
	rm -f ../bin/vf-cxx-ast-exporter$(DOTEXE)
	cd $(CXX_FE_AST_EXPORTER_DIR) && cmake --build build --target clean
	rm -f $(CXX_FE_DIR)/*.cm* $(CXX_FE_STUBS_DIR)/*.cm* $(CXX_FE_DIR)/*.cm*
	rm -f $(CXX_FE_DIR)/*.o $(CXX_FE_STUBS_DIR)/*.o $(CXX_FE_DIR)/*.o
	rm -f $(CXX_FE_STUBS_DIR)/stubs_ast.ml*
