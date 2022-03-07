# This Makefile makes sense as a part of ../GNUmakefile.
# In case of interest in one of its targets use the parent makefile
# with the target name

BIN_DIR = ../bin
RUST_FE_DIR = rust_frontend

MIR_EXP_DIR = $(RUST_FE_DIR)/mir_exporter
VF_MIR_DIR = $(RUST_FE_DIR)/vf_mir
VF_MIR_SCHEMA = $(VF_MIR_DIR)/vf_mir.capnp

VF_RUST_MIR_EXPORTER_BIN = $(BIN_DIR)/vf-rust-mir-exporter$(DOTEXE)
VF_RUST_MIR_OCAML_STUBS = $(VF_MIR_DIR)/vf_mir.mli $(VF_MIR_DIR)/vf_mir.ml

build-rust-frontend: $(VF_RUST_MIR_EXPORTER_BIN) $(VF_RUST_MIR_OCAML_STUBS)

# The Rust side
# TODO @Nima: Handle the rust build profile and the corresponding address
# TODO @Nima: Send $(VF_MIR_SCHEMA) path from here to mir_exporter cargo project
$(VF_RUST_MIR_EXPORTER_BIN):
	cd $(MIR_EXP_DIR) && cargo build
	cp $(MIR_EXP_DIR)/target/debug/mir_exporter $@

.PHONY: $(VF_RUST_MIR_EXPORTER_BIN)
# TODO @Nima: Is there a better way to trigger cargo builds when it is necessary?

clean::
	cd $(MIR_EXP_DIR) && cargo clean
	rm -f $(VF_RUST_MIR_EXPORTER_BIN)

# The OCaml side
$(VF_RUST_MIR_OCAML_STUBS) &:: $(VF_MIR_SCHEMA)
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS) capnp compile -I $(CAPNP_INCLUDE) -o ocaml:$(VF_MIR_DIR) $<

clean::
	rm -f $(VF_RUST_MIR_OCAML_STUBS)