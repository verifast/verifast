let _ =
  Verifast.register_prover "redux"
    (
      fun client ->
        let ctxt = (new Redux.context: Redux.context :> (unit, Redux.symbol, (Redux.symbol, Redux.termnode) Redux.term) Proverapi.context) in
        client#run ctxt
    )
