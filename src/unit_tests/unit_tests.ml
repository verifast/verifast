let () = Printexc.record_backtrace true
let () =
  print_endline "============================================================";
  print_endline "  VeriFast Comprehensive OCaml Unit Test Suite";
  print_endline "============================================================";

  let suites = [
    ("Test_simplex", Test_simplex.run);
    ("Test_provers", Test_provers.run);
    ("Test_sexpr_smtlib", Test_sexpr_smtlib.run);
    ("Test_frontend_parser", Test_frontend_parser.run);
    ("Test_rust_translator", Test_rust_translator.run);
  ] in

  let total_assertions = ref 0 in
  let failed_suites = ref 0 in

  List.iter (fun (name, run_suite) ->
    try
      let count = run_suite () in
      total_assertions := !total_assertions + count;
      Printf.printf "  [PASS] %-25s : %3d assertions passed\n" name count
    with exn ->
      incr failed_suites;
      Printf.eprintf "  [FAIL] %-25s : exception %s\nBacktrace:\n%s\n" name (Printexc.to_string exn) (Printexc.get_backtrace ())
  ) suites;

  print_endline "============================================================";
  if !failed_suites = 0 then (
    Printf.printf "  RESULT: ALL SUITES PASSED! Total %d assertions verified.\n" !total_assertions;
    print_endline "============================================================";
    exit 0
  ) else (
    Printf.eprintf "  RESULT: %d SUITE(S) FAILED!\n" !failed_suites;
    print_endline "============================================================";
    exit 1
  )

let () =
  (try Vf_cov_runtime.dump_stats () with _ -> ())
