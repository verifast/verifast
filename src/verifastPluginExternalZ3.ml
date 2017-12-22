module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi

let _ =
  Verifast.register_prover "ext_z3"
    "\brun Z3 as an external prover. This is to measure the impact of communicating with Z3 using a pipe instead of the API. This is also more portable."
    (
      fun client ->
      let z3_ctxt =
        Sp.external_smtlib_ctxt
          "z3 -in -smt2 smt.auto_config=false smt.mbqi=false auto_config=false model=false type_check=true well_sorted_check=true"
          ["z3"; "I"; "Q"; "NDT"; "LIA"; "LRA"]
      in
      client#run z3_ctxt
    )
