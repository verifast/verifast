all: VfMir.vo Annotations.vo Values.vo SymbolicExecution.vo AxSem.vo LogicalHeaps.vo SymexSoundness.vo

clean:
	rm -f *.vo* *.glob

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

LogicalHeaps.vo: LogicalHeaps.v SymbolicExecution.vo
	coqc -R . VeriFast LogicalHeaps.v

SymexSoundness.vo: SymexSoundness.v AxSem.vo LogicalHeaps.vo
	coqc -R . VeriFast SymexSoundness.v
