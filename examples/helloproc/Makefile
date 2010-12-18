# -------------------------------------------------------------------- #
# Configuration of this kernel module
# -------------------------------------------------------------------- #

# See Makefile_template.make for information.

MODULE_FINAL_OBJ := helloproc.o
MODULE_INIT_OBJ := helloproc_main.o
MODULE_OBJS := 
CONFIG_MODULE_OR_BUILTIN := m

# Just leave as it is:
ifeq ($(origin src), undefined)
	include vf_buildsystem.make
else
	include $(src)/vf_buildsystem.make
endif

