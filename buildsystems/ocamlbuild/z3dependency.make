#
# Checks Z3 dependency and sets variables for it.
# Does not build Z3 bindings.
# Safe to include if you do not force a dependency on Z3.
# 

ifndef Z3DEPENDENCY_INCLUDED
  Z3DEPENDENCY_INCLUDED = yes

include init.make

ifdef Z3
  INCLUDECODE_Z3 = $(SRCDIR)/verifastPluginZ3.ml
else ifdef Z3V2
  Z3 = $(Z3V2)
  INCLUDECODE_Z3 += $(SRCDIR)/verifastPluginZ3v2.ml
else ifdef Z3V4
  Z3 = $(Z3V4)
  INCLUDECODE_Z3 += $(SRCDIR)/verifastPluginZ3v4.ml
else ifdef NOZ3
else
z3maybe:
	$(error Please define NOZ3,Z3,Z3V2 or Z3V4 (e.g. make NOZ3=1))
endif

ifdef NOZ3
  ifdef Z3
    z3maybe:
	$(error You both defined the NOZ3 variable and a Z3,Z3V2 or Z3V4 variable.)
  endif
endif

ifdef Z3
  LDLPATH += $(Z3)/lib
  OCAMLBUILDFLAGS_Z3 += -libs z3
  OCAMLBUILDFLAGS_Z3 += -cflags -I,$(Z3)/ocaml -lflags -I,$(Z3)/ocaml
  OCAMLBUILDFLAGS_Z3 += -lflags -ccopt,-I$(Z3)/ocaml,-ccopt,-L$(Z3)/bin,-ccopt,-L$(Z3)/lib
  OCAMLBUILDFLAGS_Z3 += -lflags -cclib,-lz3-gmp,-cclib,-lz3stubs,$(OCAMLLIB)/libcamlidl.a
  
  # Actually this should also include the 
  FILES_MUSTBEFOUND = $(Z3)/lib/libz3.so $(Z3)/lib/libz3-gmp.so $(Z3)/ocaml/z3.cmxa $(Z3)/ocaml/z3.cmi
  FILES_FOUND = $(wildcard $(FILES_MUSTBEFOUND))
  FILES_NOT_FOUND=$(filter-out $(FILES_FOUND),$(FILES_MUSTBEFOUND))
  ifneq ($(FILES_NOT_FOUND),)
    $(error You set an incorrect Z3 path or forgot to combine the Z3 bindings. Files I expected but could not find: $(FILES_NOT_FOUND))
  endif
  z3maybe:
endif

endif
