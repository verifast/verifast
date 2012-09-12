verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.c
verifast -shared -emit_vfmanifest ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.c
verifast -shared -emit_vfmanifest ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest map.c
verifast -shared -emit_vfmanifest ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest set.c
verifast -shared -emit_vfmanifest ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest wfmap.c

verifast -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest sset.c
verifast -allow_assume -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest map.vfmanifest mutex3.vfmanifest ..\..\..\bin\threading.vfmanifest sset.c cset.c
verifast -allow_assume -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest map.vfmanifest mutex3.vfmanifest ..\..\..\bin\threading.vfmanifest set.vfmanifest slist.vfmanifest sset.c wfmap.vfmanifest fset.c
verifast -allow_assume -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest map.vfmanifest mutex3.vfmanifest ..\..\..\bin\threading.vfmanifest set.vfmanifest slist.vfmanifest sset.c wfmap.vfmanifest fset2.c
verifast -allow_assume -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest map.vfmanifest mutex3.vfmanifest ..\..\..\bin\threading.vfmanifest set.vfmanifest slist.vfmanifest sset.c wfmap.vfmanifest fset3.c
verifast -allow_assume -shared ..\..\..\bin\list.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest slist.vfmanifest map.vfmanifest mutex3.vfmanifest ..\..\..\bin\threading.vfmanifest set.vfmanifest slist.vfmanifest sset.c wfmap.vfmanifest fset4.c