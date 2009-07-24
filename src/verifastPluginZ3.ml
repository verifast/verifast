let _ =
  Verifast.register_prover "z3"
    "\nPowered by the excellent SMT solver Z3 <http://research.microsoft.com/projects/z3> by Leonardo de Maura and Nikolaj Bjorner. The Z3 license applies. See Z3.LICENSE.txt."
    (
      fun client ->
        let ctxt = (new Z3prover.z3_context() : Z3prover.z3_context :> (Z3.type_ast, Z3.const_decl_ast, Z3.ast) Proverapi.context) in
        client#run ctxt
    )