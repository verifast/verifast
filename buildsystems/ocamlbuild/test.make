#
# Launches VeriFast's testsuite.
#

include init.make
include verifast.make
include mysh.make
include stdlib.make

test: verifast mysh stdlib
	cd $(SRCDIR)/.. &&\
	export PATH=$PATH:$(BINDIR) &&\
	mysh -numcpu 8 < testsuite.mysh
.PHONY: test
	
