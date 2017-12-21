module Z = Z3v4dot5prover
module Zn = Z3native
module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi
module C = Combineprovers

let _ =
  Verifast.register_prover "z3v4.5+smtlib"
    "\nRun Z3 version 4.5 and perform an SMTLib dump."
    (
      fun client ->
      let z3_ctxt =
        (new Z.z3_context():
           Z.z3_context :> (Zn.sort, Zn.func_decl, Zn.ast) P.context)
      in
      let smtlib_ctxt = Sp.dump_smtlib_ctxt "z3_v4dot5_dump.smt2" in
      client#run (C.combine z3_ctxt smtlib_ctxt C.Sync)
    )
