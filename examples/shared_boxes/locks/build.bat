verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.c
verifast -shared ..\..\..\bin\threading.vfmanifest sblock.c
verifast -shared ..\..\..\bin\threading.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest tblock.c
verifast -shared ..\..\..\bin\threading.vfmanifest sglock.c