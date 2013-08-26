#
# Provides targets to other targets for launching ocamlbuild
#

ifndef RUN_OCAMLBUILD_MAKE_INCLUDED
  RUN_OCAMLBUILD_MAKE_INCLUDED = yes

include init.make

# For readability we just put the list of users here. From a design
# point of view we should do this distributed but that would require
# makefile magic and I want people to easily read the makefiles.
OCAMLBUILD_SUPERTARGETS = vfide verifast mysh dlsymtool main_class java_card_applet

OCAMLBUILDFLAGS += -j 16 -no-hygiene

ifdef VERBOSE
  # makes ocamlbuild print the commands it executes
  OCAMLBUILDFLAGS+=-classic-display
endif

# All warnings are errors, except a few that we hide.
OCAMLBUILDFLAGS+= -cflags -warn-error,A,-w,-8,-w,-28,-w,-26,-w,-10

ifdef DEBUG
OCAMLBUILDFLAGS += -cflags -g
endif

ifdef BYTECODE
OCAMLBUILD_KIND=byte
OCAMLBUILDFLAGS += -lflags -custom
else
OCAMLBUILD_KIND=native
endif

# ocamlbuild has the weirdest behaviour (e.g. creating a Windows
# executable on Linux) if the SRCDIR directory contains building
# output files. Other build tools sometimes put their garbage there.
clean_external:
	rm -f $(wildcard $(addprefix $(SRCDIR)/, *.cm* *.o *.a))

$(addprefix run_ocamlbuild_,$(OCAMLBUILD_SUPERTARGETS)): clean_external ocamlbuild
	cat $(INCLUDECODE) $(SRCDIR)/$(SRCNAME) > $(SRCDIR)/buildcat_$(BINNAME).ml &&\
	mkdir -p $(BUILDDIR) &&\
	cd $(SRCDIR) &&\
	export CYGWIN=nodosfilewarning &&\
	export LD_LIBRARY_PATH=$(LD_LIBRARY_PATH):$(LDLPATH) &&\
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) -build-dir $(BUILDDIR)/$(BINNAME) buildcat_$(BINNAME).$(OCAMLBUILD_KIND) &&\
	cp $(BUILDDIR)/$(BINNAME)/buildcat_$(BINNAME).$(OCAMLBUILD_KIND) $(BINDIR)/$(BINNAME)$(DOTEXE) &&\
	chmod +x $(BINDIR)/$(BINNAME)$(DOTEXE)
	
	
.PHONY: $(addprefix run_ocamlbuild_,$(OCAMLBUILDSUBTARGETS)) &&\


run_ocamlbuild:
	$(error Internal error: target run_ocamlbuild must not be used, use run_ocamlbuild_SUBTARGETNAME)


clean::
	rm -f $(SRCDIR)/buildcat_*.ml

endif
