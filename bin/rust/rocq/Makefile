all: VfMir.vo Annotations.vo SymbolicExecution.vo

clean:
	rm *.vo* *.glob

VfMir.vo: VfMir.v
	coqc -R . VeriFast VfMir.v

Annotations.vo: Annotations.v VfMir.vo
	coqc -R . VeriFast Annotations.v

SymbolicExecution.vo: SymbolicExecution.v Annotations.vo
	coqc -R . VeriFast SymbolicExecution.v
