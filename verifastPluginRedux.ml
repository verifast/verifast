let _ =
  Verifast2.register_prover "redux"
    (
      fun print_stats verbose path stream reportKeyword reportGhostRange ->
        let ctxt = (new Redux.context: Redux.context :> (Redux.symbol, Redux.termnode) Proverapi.context) in
        Verifast2.verify_program_with_stats ctxt print_stats verbose path stream reportKeyword reportGhostRange
    )
