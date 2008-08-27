let _ =
  Verifast.register_prover "redux"
    (
      fun client ->
        let ctxt = (new Redux.context: Redux.context :> (Redux.symbol, Redux.termnode) Proverapi.context) in
        client#run ctxt
    )
