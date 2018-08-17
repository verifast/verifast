module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi

let _ =
  Verifast.register_prover "CVC4"
    "(experimental) the CVC4 theorem prover. (Does not ship with VeriFast; make sure the 'cvc4' command is in your PATH.)"
    (
      fun client ->
      let cvc4_ctxt =
        Sp.external_smtlib_ctxt
          "cvc4 --incremental --lang smt"
          ["cvc4"; "I"; "Q"; "NDT"; "LIA"; "LRA"]
      in
      client#run cvc4_ctxt
    )
