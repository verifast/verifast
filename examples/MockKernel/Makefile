all: MockKernel_exe AdderModule_dll

MockKernel_exe:
	dlsymtool MockKernelModule.dlsymspec
	cl /D_CRT_SECURE_NO_DEPRECATE /MDd /Zi /D_DEBUG /DWIN32 /DMOCKKERNEL_EXPORTS MockKernel.c MockKernelModule_proxy.c threading.c stringBuffers.c lists.c sockets.c libraries.c ws2_32.lib MockKernel.def

AdderModule_dll:
	cl /MDd /Zi /D_DEBUG /DWIN32 /LD AdderModule.c MockKernel.lib AdderModule.def

clean:
	del *.exe *.dll *.exp *.lib *.obj *.pdb *.manifest *.ilk
