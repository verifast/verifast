@echo off
echo ------------------------------------------------------------
echo libraries first
echo ------------------------------------------------------------
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest lset.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest lset.vfmanifest dlset.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest lmultiset.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest lset.vfmanifest lmultiset.vfmanifest lmultisetandset.c

verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest ghost_counters.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest ghost_lists.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest ghost_pairs.c

verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest fraction_store.c

verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest cperm.c
verifast -shared -emit_vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest fraction_store.vfmanifest space_user.c


echo ------------------------------------------------------------
echo some examples now 
echo ------------------------------------------------------------
verifast -shared atomics.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest fraction_store.vfmanifest fraction_store_example.c
verifast -shared atomics.vfmanifest mutex_impl.c
verifast -shared atomics.vfmanifest ..\..\..\bin\threading.vfmanifest singleton_buffer.c
verifast -shared atomics.vfmanifest ..\..\..\bin\listex.vfmanifest cperm.vfmanifest test_node_tracker.c
verifast -shared atomics.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest fraction_store.vfmanifest space_user.vfmanifest space_user_example.c

echo ------------------------------------------------------------
echo real stuff now
echo ------------------------------------------------------------
verifast -shared atomics.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest linkedlist.c
verifast -shared atomics.vfmanifest stack_leaking.c
verifast -shared atomics.vfmanifest ..\..\..\bin\listex.vfmanifest listex2.vfmanifest lset.vfmanifest lmultiset.vfmanifest lmultisetandset.vfmanifest atomics_int.vfmanifest atomics_bool.vfmanifest cperm.vfmanifest  ghost_lists.vfmanifest linkedlist.c stack_hp.c
