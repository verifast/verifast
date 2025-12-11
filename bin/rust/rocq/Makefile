all: VfMir.vo Annotations.vo Values.vo SymbolicExecution.vo AxSem.vo

clean:
	rm *.vo* *.glob

VfMir.vo: VfMir.v
	coqc -R . VeriFast VfMir.v

Annotations.vo: Annotations.v VfMir.vo
	coqc -R . VeriFast Annotations.v

Values.vo: Values.v Annotations.vo
	coqc -R . VeriFast Values.v

SymbolicExecution.vo: SymbolicExecution.v Annotations.vo
	coqc -R . VeriFast SymbolicExecution.v

AxSem.vo: AxSem.v Values.vo SymbolicExecution.vo
	coqc -R . VeriFast AxSem.v