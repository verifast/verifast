threads0.exe: threads0.c
	cl threads0.c

threads.exe: threads.c
	cl /c /I $(VERIFAST_BINDIR) /I ..\examples threads.c
	cl /DWIN32 threads.obj $(VERIFAST_BINDIR)\threading.c
