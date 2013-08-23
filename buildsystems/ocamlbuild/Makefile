#
# Entry point for when user types "make".
#
# 
# Usage: make [target] [PARAMETERS]
#
# Parameters:
#     DEBUG=1   : enables debug build
#     VERBOSE=1 : see more info scrolling by while building.
#     BYTECODE=1: compile to bytecode instead of to native code
#                 (note: migt result in a file containing also the
#                        runtime system. On e.g. Linux this will
#                        thus be an ELF file but it contains bytecode)
#     Z3=<path> : Z3 path
#     Z3v2
#     Z3v4
#     NOZ3      : Do not build with Z3
#
# Example:
#   make verifast DEBUG=1 VERBOSE=1 Z3=$HOME/compiledstuff/z3
#

default: verifast vfide test

include verifast.make
include vfide.make
include vfcommon.make
include stdlib.make
include mysh.make
include test.make

