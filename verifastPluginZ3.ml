let _ =
  Verifast2.register_prover "z3"
    (
      fun client ->
        let ctxt = (new Z3prover.z3_context() : Z3prover.z3_context :> (Z3.const_decl_ast, Z3.ast) Proverapi.context) in
        client#run ctxt
    )