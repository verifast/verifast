ifndef VFCOMMON_MAKE_INCLUDED
  VFCOMMON_MAKE_INCLUDED = yes

include init.make

ifeq ($(OS), linux)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux
endif
ifeq ($(OS), win)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/win -lflags -I,$(SRCDIR)/win
endif
ifeq ($(OS), macos)
  OCAMLBUILDFLAGS+= -cflags -I,$(SRCDIR)/linux -lflags -I,$(SRCDIR)/linux -I macos
endif

OCAMLBUILDFLAGS+= -j 16 -no-hygiene -pp camlp4o.opt -libs Perf,nums,dynlink

$(addprefix run_ocamlbuild_,$(OCAMLBUILDSUBTARGETS)): clean_external $(OS) ocamlbuild ocamlfind
	cat $(INCLUDECODE) $(SRCDIR)/$(SRCNAME) > $(SRCDIR)/buildcat_$(BINNAME).ml ;\
	mkdir -p $(BUILDDIR) ;\
	cd $(SRCDIR) ;\
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) -build-dir $(BUILDDIR)/$(BINNAME) buildcat_$(BINNAME).native;\
	cp $(BUILDDIR)/$(BINNAME)/buildcat_$(BINNAME).native $(BINDIR)/$(BINNAME)
.PHONY: $(addprefix run_ocamlbuild_,$(OCAMLBUILDSUBTARGETS))

run_ocamlbuild:
	$(error Internal error: target run_ocamlbuild must not be used, use run_ocamlbuild_SUBTARGETNAME)

clean_external:
	rm -f $(wildcard $(addprefix $(SRCDIR)/, *.cmx *.o *.a))

linux_or_macos: make
	make -C $(SRCDIR)/linux OCAMLOPTOPT=$(OCAMLOPT)

linux: linux_or_macos
	cp $(SRCDIR)/Fonts_default.ml $(SRCDIR)/Fonts.ml

macos: linux_or_macos
	cp $(SRCDIR)/Fonts_mac.ml $(SRCDIR)/Fonts.ml

clean::
	rm -fr $(BUILDDIR)
	rm -f $(SRCDIR)/buildcat_*.ml
	rm -f $(SRCDIR)/linux/*.o
	rm -f $(SRCDIR)/linux/*.a
	rm -f $(SRCDIR)/linux/*.cm*
	rm -f $(SRCDIR)/macos/*.o
	rm -f $(SRCDIR)/macos/*.a
	rm -f $(SRCDIR)/macos/*.cm*
	rm -f $(SRCDIR)/win/*.o
	rm -f $(SRCDIR)/win/*.a
	rm -f $(SRCDIR)/win/*.cm*
	rm -f $(SRCDIR)/win/*.dll

endif
