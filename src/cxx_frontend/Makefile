# Don't run this file directly, use the one in src, which inlcudes this one.
# All targets/recipes are relative to src.

CXX_FE_DIR					= cxx_frontend
CXX_FE_STUBS_DIR			= $(CXX_FE_DIR)/stubs
CXX_FE_AST_EXPORTER_DIR		= $(CXX_FE_DIR)/ast_exporter

CAPNP_BIN			?= $(shell dirname `which capnp`)
CAPNP_INCLUDE		?= $(CAPNP_BIN)/../include

ifeq ($(OS), Windows_NT)
CAPNP_INCLUDE := $(shell cygpath -w $(CAPNP_INCLUDE))
endif

export CAPNP_INCLUDE

../bin/libstdc++-6.dll: /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libstdc++-6.dll
	cp -f $< $@

ifeq ($(OS), Windows_NT)
../bin/vf-cxx-ast-exporter$(DOTEXE): ../bin/libstdc++-6.dll
endif
../bin/vf-cxx-ast-exporter$(DOTEXE): $(CXX_FE_STUBS_DIR)/stubs_ast.capnp $(CXX_FE_AST_EXPORTER_DIR)/*.h $(CXX_FE_AST_EXPORTER_DIR)/*.cpp
	@echo "  MAKE " $@
	cd $(CXX_FE_AST_EXPORTER_DIR) && mkdir -p build
	cd $(CXX_FE_AST_EXPORTER_DIR) && if [ ! -f build/CMakeCache.txt ]; then \
		if [ "$(OS)" = "Darwin" ]; then \
			LLVM_INSTALL_DIR="/usr/local/vf-llvm-clang-build-$(VF_LLVM_CLANG_BUILD_VERSION)"; \
			VFDEPS_DIR="/usr/local/$(VFDEPS_NAME)"; \
		else \
			LLVM_INSTALL_DIR="/tmp/vf-llvm-clang-build-$(VF_LLVM_CLANG_BUILD_VERSION)"; \
			VFDEPS_DIR="/tmp/$(VFDEPS_NAME)"; \
		fi; \
		cmake -S . -B build -DLLVM_INSTALL_DIR="$$LLVM_INSTALL_DIR" -DVFDEPS="$$VFDEPS_DIR" -DCMAKE_BUILD_TYPE=Release; \
	fi
	cd $(CXX_FE_AST_EXPORTER_DIR) && cmake --build build
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && mv vf-cxx-ast-exporter$(DOTEXE) ../../../$@

stubs: $(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++
.PHONY: stubs

clean::
	rm -f ../bin/vf-cxx-ast-exporter$(DOTEXE)
	cd $(CXX_FE_AST_EXPORTER_DIR) && cmake --build build --target clean
