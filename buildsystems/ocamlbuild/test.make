include init.make
include verifast.make
include mysh.make
include stdlib.make

test: verifast mysh stdlib
	cd $(SRCDIR)/.. ; mysh -numcpu 8 < testsuite.mysh ; echo Note: because of a bug of mysh the tests fails.
.PHONY: test
	
