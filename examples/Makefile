chat.exe:
	cl /MDd /c /DWIN32 /I $(VERIFAST_BINDIR) chat.c lists.c stringBuffers.c
	cl /MDd /DWIN32 chat.obj lists.obj stringBuffers.obj ws2_32.lib sockets.c $(VERIFAST_BINDIR)\threading.c

bot.exe:
	cl /MDd /DWIN32 bot.c stringBuffers.c ws2_32.lib sockets.c