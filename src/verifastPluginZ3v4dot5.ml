let _ =
  Verifast.register_prover "z3v4.5"
    "\nPowered by the excellent SMT solver Z3 <https://github.com/Z3Prover/z3> by Leonardo de Moura and Nikolaj Bjorner at Microsoft Research, and contributors. The Z3 license (an MIT license) applies. See Z3.LICENSE.txt."
    (
      fun client ->
        let ctxt = (new Z3v4dot5prover.z3_context() : Z3v4dot5prover.z3_context :> (Z3native.sort, Z3native.func_decl, Z3native.ast) Proverapi.context) in
        client#run ctxt
    )
