module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi

let _ =
  Verifast.register_prover "cvc4"
    "\brun CVC4."
    (
      fun client ->
      let cvc4_ctxt =
        Sp.external_smtlib_ctxt "cvc4 --incremental --lang smt" in
      client#run cvc4_ctxt
    )
