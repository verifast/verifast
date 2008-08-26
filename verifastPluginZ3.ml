let _ =
  Verifast2.register_prover "z3"
    (
      fun print_stats verbose path stream reportKeyword reportGhostRange ->
        let ctxt = (new Z3prover.z3_context() : Z3prover.z3_context :> (Z3.const_decl_ast, Z3.ast) Proverapi.context) in
        Verifast2.verify_program_with_stats ctxt print_stats verbose path stream reportKeyword reportGhostRange
    )