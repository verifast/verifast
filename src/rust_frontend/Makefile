# This Makefile makes sense as a part of ../GNUmakefile.
# In case of interest in one of its targets use the parent makefile
# with the target name

CAPNP_BIN ?= $(shell dirname `which capnp`)
CAPNP_INCLUDE ?= $(CAPNP_BIN)/../include
CAPNP_LIBS ?= $(CAPNP_BIN)/../lib
CAPNP_LINK_FLAGS = -package capnp,capnp.unix
# Rename to comply with our naming convention
CAPNP = capnp
CAPNP_INC_DIR = $(CAPNP_INCLUDE)
CAPNP_LIBS_DIR = $(CAPNP_LIBS)

BIN_DIR = ../bin

RUST_FE_DIR ?= rust_frontend
RUST_FE_INC = $(RUST_FE_DIR)
RUST_FE_SRC = $(RUST_FE_DIR)/rust_fe.ml
RUST_FE_OBJ = $(RUST_FE_DIR)/rust_fe.cmx
OCAML_AUX_SRC = $(RUST_FE_DIR)/ocaml_aux.ml
OCAML_AUX_OBJ = $(RUST_FE_DIR)/ocaml_aux.cmx

VF_MIR_EXP_DIR = $(RUST_FE_DIR)/vf_mir_exporter
VF_MIR_EXP_BIN = $(BIN_DIR)/vf-rust-mir-exporter$(DOTEXE)

VF_MIR_DIR = $(RUST_FE_DIR)/vf_mir
VF_MIR_SCHEMA = $(VF_MIR_DIR)/vf_mir.capnp

VF_MIR_OCAML_STUBS_DIR = $(VF_MIR_DIR)
VF_MIR_OCAML_STUBS_SRC = $(VF_MIR_OCAML_STUBS_DIR)/vf_mir.mli $(VF_MIR_OCAML_STUBS_DIR)/vf_mir.ml
VF_MIR_OCAML_STUBS_OBJ = $(VF_MIR_OCAML_STUBS_DIR)/vf_mir.cmx

VF_MIR_TRANSLATOR_DIR = $(RUST_FE_DIR)/vf_mir_translator
VF_MIR_ANNOT_PARSER_SRC = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_annot_parser.ml
VF_MIR_ANNOT_PARSER_OBJ = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_annot_parser.cmx
VF_MIR_CAPNP_ALIAS_SRC = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_capnp_alias.ml
VF_MIR_CAPNP_ALIAS_OBJ = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_capnp_alias.cmx
VF_MIR_TRANSLATOR_SRC = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_translator.ml
VF_MIR_TRANSLATOR_OBJ = $(VF_MIR_TRANSLATOR_DIR)/vf_mir_translator.cmx

# The Rust side
# TODO @Nima: Handle the rust build profile and the corresponding address
# TODO @Nima: Send $(VF_MIR_SCHEMA) path from here to mir_exporter cargo project
$(VF_MIR_EXP_BIN):
	cd $(VF_MIR_EXP_DIR) && cargo build
	@cp $(VF_MIR_EXP_DIR)/target/debug/vf_mir_exporter $@

.PHONY: $(VF_MIR_EXP_BIN)
# TODO @Nima: Is there a better way to trigger cargo builds when it is necessary?

clean::
	cd $(VF_MIR_EXP_DIR) && cargo clean
	@rm -f $(VF_MIR_EXP_BIN)

# The OCaml side
$(VF_MIR_OCAML_STUBS_SRC) &:: $(VF_MIR_SCHEMA)
	@echo "  CAPNP " $<
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS_DIR) $(CAPNP) compile -I $(CAPNP_INC_DIR) -o ocaml:$(VF_MIR_DIR) $<

clean::
	rm -f $(VF_MIR_OCAML_STUBS_SRC)

$(VF_MIR_OCAML_STUBS_OBJ): $(VF_MIR_OCAML_STUBS_SRC)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11-55 -I $(VF_MIR_OCAML_STUBS_DIR) $(CAPNP_LINK_FLAGS) $^

clean::
	rm -f $(VF_MIR_OCAML_STUBS_DIR)/*.cm* $(VF_MIR_OCAML_STUBS_DIR)/*.o

$(VF_MIR_ANNOT_PARSER_OBJ): $(VF_MIR_ANNOT_PARSER_SRC)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 $<
$(VF_MIR_CAPNP_ALIAS_OBJ): $(VF_MIR_CAPNP_ALIAS_SRC) $(VF_MIR_OCAML_STUBS_OBJ)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 -I $(VF_MIR_OCAML_STUBS_DIR) -package capnp $<
$(VF_MIR_TRANSLATOR_OBJ): $(VF_MIR_TRANSLATOR_SRC) $(OCAML_AUX_OBJ) $(VF_MIR_ANNOT_PARSER_OBJ) $(VF_MIR_CAPNP_ALIAS_OBJ) ast.cmx
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 -I $(RUST_FE_INC) -I $(VF_MIR_TRANSLATOR_DIR) -package capnp $<

clean::
	rm -f $(VF_MIR_TRANSLATOR_DIR)/*.cm* $(VF_MIR_TRANSLATOR_DIR)/*.o

$(OCAML_AUX_OBJ): $(OCAML_AUX_SRC)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 $<

# The whole frontend interface
$(RUST_FE_OBJ): $(RUST_FE_SRC) $(OCAML_AUX_OBJ) $(VF_MIR_TRANSLATOR_OBJ)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 -I $(RUST_FE_INC) -I $(VF_MIR_TRANSLATOR_DIR) -I $(VF_MIR_OCAML_STUBS_DIR) $(CAPNP_LINK_FLAGS) $<

clean::
	rm -f $(RUST_FE_DIR)/*.cm* $(RUST_FE_DIR)/*.o

# Use this variable in parent Makefile to link to Rust frontend
RUST_FE_OBJS = $(OCAML_AUX_OBJ) $(VF_MIR_OCAML_STUBS_OBJ) $(VF_MIR_ANNOT_PARSER_OBJ) $(VF_MIR_CAPNP_ALIAS_OBJ) $(VF_MIR_TRANSLATOR_OBJ) $(RUST_FE_OBJ)
# VF MIR exporter tool
build-vf-rust-mir-exporter: $(VF_MIR_EXP_BIN)
# Rust frontend
build-rust-frontend: build-vf-rust-mir-exporter $(RUST_FE_OBJS)