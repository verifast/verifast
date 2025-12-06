all: VfMir.vo

clean:
	rm *.vo* *.glob

VfMir.vo: VfMir.v
	coqc -R . VeriFast VfMir.v
