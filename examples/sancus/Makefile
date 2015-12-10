
SANCUS_SETENV=$(shell cat ../sancus-setenv)
VF_SETENV=export PATH=$(shell cat ../../verifast/path_to_verifast):$$PATH;

VFIDE=${VF_SETENV} vfide

CC=${SANCUS_SETENV} sancus-cc
LD=${SANCUS_SETENV} sancus-ld
SIM=${SANCUS_SETENV} sancus-sim
CRYPTO=${SANCUS_SETENV} sancus-crypto
LOAD=${SANCUS_SETENV} sancus-loader

OBJECTS=example.o
TARGET=example.elf
TARGET_NO_MACS=$(TARGET).no-macs
VKEY=4078d505d82099ba
ROM=48K
RAM=10K

CFLAGS=
LIBS=

all: $(TARGET) vfide

$(TARGET_NO_MACS): $(OBJECTS) $(LIBS)
	$(LD) --standalone --rom $(ROM) --ram $(RAM) -o $@ $^

$(TARGET): $(TARGET_NO_MACS)
	$(CRYPTO) --key $(VKEY) -o $@ $<

sim: $(TARGET)
	$(SIM) --rom $(ROM) --ram $(RAM) $<

load: $(TARGET)
	$(LOAD) -device /dev/ttyUSB0 -baudrate 115200 $<

vfide:
	${VFIDE} -I ./vfinclude  example.c

vfbugs: example_vf_bugs.c
	${VFIDE} example_vf_bugs.c

clean:
	rm -f $(OBJECTS) $(TARGET_NO_MACS) $(TARGET)
	rm -f sancus_sim.fst sim-input.bin sim-output.bin

distclean: clean


