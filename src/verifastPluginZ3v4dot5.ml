let register_plugin () =
  Verifast.register_prover "Z3v4.5"
    "the Z3 SMT solver <https://github.com/Z3Prover/z3> by Leonardo de Moura and Nikolaj Bjorner at Microsoft Research, and contributors."
    (
      fun client ->
        let ctxt = (new Z3v4dot5prover.z3_context() : Z3v4dot5prover.z3_context :> (Z3native.sort, Z3native.func_decl, Z3native.ast) Proverapi.context) in
        client#run ctxt
    )
