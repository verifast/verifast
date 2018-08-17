let _ =
  Verifast.register_prover "Z3"
    "the Z3 SMT solver <http://research.microsoft.com/projects/z3> by de Maura and Bjorner. The Z3 license applies. See Z3.LICENSE.txt."
    (
      fun client ->
        let ctxt = (new Z3prover.z3_context() : Z3prover.z3_context :> (Z3.type_ast, Z3.const_decl_ast, Z3.ast) Proverapi.context) in
        client#run ctxt
    )
