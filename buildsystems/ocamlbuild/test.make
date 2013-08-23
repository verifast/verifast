#
# Launches VeriFast's testsuite.
#

include init.make
include verifast.make
include mysh.make
include stdlib.make
include dlsymtool.make
include main_class.make
include java_card_applet.make

test: verifast mysh stdlib dlsymtool main_class java_card_applet
	cd $(SRCDIR)/.. &&\
	export PATH=$PATH:$(BINDIR) &&\
	mysh -cpus 8 < testsuite.mysh
.PHONY: test
	
