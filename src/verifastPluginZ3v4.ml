let _ =
  (* I had some issues with a wrong LD_LIBRARY_PATH... *)
  Z3v4prover.display_version();
  Verifast.register_prover "z3"
    "\nPowered by the excellent SMT solver Z3 <http://research.microsoft.com/projects/z3> by Leonardo de Maura and Nikolaj Bjorner. The Z3 license applies. See Z3.LICENSE.txt."
    (
      fun client ->
        let ctxt = (new Z3v4prover.z3_context() : Z3v4prover.z3_context :> (Z3.sort, Z3.func_decl, Z3.ast) Proverapi.context) in
        client#run ctxt
    )
