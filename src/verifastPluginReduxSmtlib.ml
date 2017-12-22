module R = Redux
module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi
module C = Combineprovers

let _ =
  Verifast.register_prover "redux+smtlib"
    "\nRun redux and perform an SMTLib dump."
    (
      fun client ->
      let redux_ctxt =
        (new R.context ():
           R.context :> (unit, R.symbol, (R.symbol, R.termnode) R.term) P.context)
      in
      let smtlib_ctxt =
        Sp.dump_smtlib_ctxt
          "redux_dump.smt2"
          ["dump"; "I"; "Q"; "NDT"; "LIA"; "LRA"]
      in
      client#run (C.combine redux_ctxt smtlib_ctxt C.Sync)
    )
