let _ =
  Verifast.register_prover "Redux"
    "the built-in Redux theorem prover. A partial re-implementation in OCaml by the VeriFast team of the Simplify theorem prover [Detlefs, Nelson, and Saxe]."
    (
      fun client ->
        let ctxt = (new Redux.context (): Redux.context :> (unit, Redux.symbol, (Redux.symbol, Redux.termnode) Redux.term) Proverapi.context) in
        client#run ctxt
    )
