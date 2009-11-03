threads0.exe: threads0.c
	cl threads0.c

threads.exe: threads.c
	cl /c /I $(VERIFAST_BINDIR) /I ..\examples threads.c
	cl /DWIN32 threads.obj $(VERIFAST_BINDIR)\threading.c

fractions.exe: fractions.c
	cl /c /I $(VERIFAST_BINDIR) /I ..\examples fractions.c
	cl /DWIN32 fractions.obj $(VERIFAST_BINDIR)\threading.c
