all: BeepKernel_exe BeepDriver_dll

BeepKernel_exe:
	dlsymtool BeepDriver.dlsymspec
	cl /D_CRT_SECURE_NO_DEPRECATE /MDd /Zi /D_DEBUG /DWIN32 BeepKernel.c BeepDriver_proxy.c Modules.c libraries.c BeepKernel.def

BeepDriver_dll:
	cl /MDd /Zi /D_DEBUG /DWIN32 /LD BeepDriver.c BeepKernel.lib BeepDriver.def

clean:
	del *.exe *.dll *.exp *.lib *.obj *.pdb *.manifest *.ilk
