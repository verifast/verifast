# -------------------------------------------------------------------- #
# Configuration of this kernel module
# -------------------------------------------------------------------- #

# Make a copy of this file to a file named "Makefile" and
# fill in the fields.



# Final name of the kernel module: (including .o extension)
#
# Example: MODULE_FINAL_OBJ := mymodule.o
MODULE_FINAL_OBJ := 

# .o file of the kernel module which contains the init and exit
# procedures (including .o extension).
# See vf_initexit.h for information about how to write these procedures.
#
# Example: MODULE_INIT_OBJ := mymodule_main.o
MODULE_INIT_OBJ := 

# .o files of the kernel module, *** excluding MODULE_INIT_OBJ ***.
# (including the .o extension). If x.o depends on y.o, put y.o first.
#
# Example: MODULE_OBJS := mymodule_inode.o mymodule_somethingelse.o
MODULE_OBJS := 

# "m" (without quotes) for module, "y" for builtin, "n" for not building
#
# Example: CONFIG_MODULE_OR_BUILTIN := m
CONFIG_MODULE_OR_BUILTIN := m

# You can set KERNELDIR if you would like to use an alternative
# kernel directory to compile to.  Otherwise, just leave it undefined
# by leaving it commented out.
#KERNELDIR := /lib/modules/$(shell uname -r)/build

# Start up the vf_buildsystem, just leave the following lines as they
# are:
ifeq ($(origin src), undefined)
	include vf_buildsystem.make
else
	include $(src)/vf_buildsystem.make
endif

