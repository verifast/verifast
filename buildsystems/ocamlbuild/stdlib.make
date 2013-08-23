#
# Executing VeriFast on the implementation/proofs of VeriFast's standard library.
# This generates .vfmanifest files, which tells further invocations of
# VeriFast that the lemmas are proven.
#

ifndef STDLIB_MAKE_INCLUDED
  STDLIB_MAKE_INCLUDED = yes

include init.make
include verifast.make

STDLIB_FILES:=list listex arrays raw_ghost_lists quantifiers permutations assoclist
STDLIB_FILES_VFMANIFEST:=$(addsuffix .vfmanifest,$(STDLIB_FILES))
STDLIB_FILES_C:=$(addsuffix .c,$(STDLIB_FILES))

$(STDLIB_FILES_C): %.c: $(BINDIR)/%.c
.PHONY: $(STDLIB_FILES_C)

$(STDLIB_FILES_VFMANIFEST): %.vfmanifest: %.c verifast
	cd $(BINDIR) ; ./verifast -c -emit_vfmanifest $<
.PHONY: $(STDLIB_FILES_VFMANIFEST)


stdlib: $(STDLIB_FILES_VFMANIFEST)
.PHONY: stdlib

clean::
	rm -f $(STDLIB_FILES_VFMANIFEST)

endif
