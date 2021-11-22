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
include $(CXX_FE_AST_EXPORTER_DIR)/MSVC_CACHE
CAPNP_INCLUDE := "$(shell cygpath -w $(CAPNP_INCLUDE))"
CAPNP_LIBS := "$(shell cygpath -w $(CAPNP_LIBS))"
BUILD_TYPE ?= Release
# cd to the dir where vcvarsall is located, because it could contain spaces and cygwin/make would not recognise the path properly
SET_MSV_ENV = pushd "%CD%" && cd /D "$(VCVARSALL_BAT_DIR)" && vcvarsall.bat x86 && popd
endif

# we specify rules here if we don't want the makefile in src to compile specific files

# ---- stubs ----
# we don't want the rule in the src/GNUmakefile to compile the stubs: 
# the camlp4 pp cannot parse '[@@@ocaml.warning ...]' attributes, which the stubs plugin generates
$(CXX_FE_STUBS_DIR)/stubs_ast.cmx: $(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -53-55 -I $(CXX_FE_STUBS_DIR) -package capnp $^

$(CXX_FE_STUBS_DIR)/stubs_ast.mli $(CXX_FE_STUBS_DIR)/stubs_ast.ml &:: $(CXX_FE_STUBS_DIR)/stubs_ast.capnp
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS) capnp compile -I $(CAPNP_INCLUDE) -o ocaml:$(CXX_FE_STUBS_DIR) $<

# ---- translator ----
CXX_TRANSL_DEPS = $(CXX_FE_STUBS_DIR)/stubs_ast.cmx $(CXX_FE_DIR)/cxx_annotation_parser.cmx $(CXX_FE_DIR)/cxx_ast_translator.ml $(CXX_FE_DIR)/cxx_ast_translator.ml

$(CXX_FE_DIR)/cxx_ast_translator.cmx: $(CXX_TRANSL_DEPS)
	@echo "  OCAMLOPT " $@
	$(COMPILE) -c -w -11 -I $(CXX_FE_STUBS_DIR) -I $(CXX_FE_DIR) -I $(CXX_FE_DIR) -package num $(CAPNP_LINK_FLAGS) $^

CXX_FE_DEPS = $(CXX_FE_STUBS_DIR)/stubs_ast.cmx $(CXX_FE_DIR)/cxx_annotation_parser.cmx $(CXX_FE_DIR)/cxx_fe_sig.cmx $(CXX_FE_DIR)/cxx_ast_translator.cmx

# ---- ast-exporter ----
$(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++ &:: $(CXX_FE_STUBS_DIR)/stubs_ast.capnp
	DYLD_LIBRARY_PATH=$(CAPNP_LIBS) capnp compile -I $(CAPNP_INCLUDE) -o c++ $<

..bin/vcruntime140.dll ../bin/msvcp140.dll:
	cp "$(shell cygpath ""$(MSVC_REDIST_DIR)"")/$(notdir $@)" ../bin

ifeq ($(OS), Windows_NT)
../bin/vf-cxx-ast-exporter$(DOTEXE): ..bin/vcruntime140.dll ../bin/msvcp140.dll
endif
../bin/vf-cxx-ast-exporter$(DOTEXE): $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.h $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.c++ $(CXX_FE_AST_EXPORTER_DIR)/*.h $(CXX_FE_AST_EXPORTER_DIR)/*.cpp
	@echo "  MAKE " $@
	@echo $(VC_REDIST_PATH_UNIX)
ifeq ($(OS), Windows_NT)
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && cmd /C "$(SET_MSV_ENV) && msbuild VF_AST_Exporter.sln -p:Configuration=$(BUILD_TYPE) -p:Platform=Win32 -m"
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && mv $(BUILD_TYPE)/vf-cxx-ast-exporter$(DOTEXE) ../../../$@
else
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && make -j$(NUMCPU)
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && mv vf-cxx-ast-exporter$(DOTEXE) ../../../$@
endif

clean::
	rm -f $(CXX_FE_STUBS_DIR)/stubs_ast.capnp.*
	rm -f ../bin/vf-cxx-ast-exporter$(DOTEXE)
ifeq ($(OS), Windows_NT)
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && cmd /C "$(SET_MSV_ENV) && msbuild VF_AST_Exporter.sln -p:Configuration=$(BUILD_TYPE) -p:Platform=Win32 -t:Clean -m"
else
	cd $(CXX_FE_AST_EXPORTER_DIR)/build && make clean
endif
	rm -f $(CXX_FE_DIR)/*.cm* $(CXX_FE_STUBS_DIR)/*.cm* $(CXX_FE_DIR)/*.cm*
	rm -f $(CXX_FE_DIR)/*.o $(CXX_FE_STUBS_DIR)/*.o $(CXX_FE_DIR)/*.o
	rm -f $(CXX_FE_STUBS_DIR)/stubs_ast.ml*