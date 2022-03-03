# This Makefile makes sense as a part of ../GNUmakefile.
# In case of interest in one of its targets use the parent makefile
# with the target name

BIN_DIR = ../bin
RUST_FE_DIR = rust_frontend
MIR_EXP_DIR = $(RUST_FE_DIR)/mir_exporter

# TODO @Nima: Handle the rust build profile and the corresponding address
$(BIN_DIR)/vf-rust-mir-exporter$(DOTEXE):
	cd $(MIR_EXP_DIR) && cargo build
	cp $(MIR_EXP_DIR)/target/debug/mir_exporter $@

.PHONY: $(BIN_DIR)/vf-rust-mir-exporter$(DOTEXE)
# TODO @Nima: Is there a better way to trigger cargo builds when it is necessary?