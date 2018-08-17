module R = Redux
module Z = Z3v4dot5prover
module Zn = Z3native
module C = Combineprovers
module P = Proverapi

let _ =
  Verifast.register_prover "Redux+Z3v4.5"
    "(experimental) run Redux and Z3v4.5 in sequence."
    (
      fun client ->
      let redux_ctxt =
        (new R.context ():
           R.context :> (unit, R.symbol, (R.symbol, R.termnode) R.term) P.context)
      in
      let z3_ctxt =
        (new Z.z3_context ():
           Z.z3_context :> (Zn.sort, Zn.func_decl, Zn.ast) P.context)
      in
      client#run (C.combine redux_ctxt z3_ctxt C.Sequence)
    )
