let test_if b =
  if b then 10 else 20

let test_match x =
  match x with
  | 1 -> 100
  | 2 -> 200
  | _ -> 300

let test_while n =
  let r = ref n in
  while !r > 0 do
    decr r
  done;
  !r

let test_for n =
  let sum = ref 0 in
  for i = 1 to n do
    sum := !sum + i
  done;
  !sum

let test_try raise_it =
  try
    if raise_it then failwith "err"
    else 42
  with Failure _ ->
    99

let read_whole_file path =
  let ic = open_in path in
  let len = in_channel_length ic in
  let buf = Bytes.create len in
  really_input ic buf 0 len;
  close_in ic;
  Bytes.to_string buf

let contains_substring sub str =
  let re = Str.regexp_string sub in
  try ignore (Str.search_forward re str 0); true with Not_found -> false

let () =
  print_endline "=== Starting Coverage Infrastructure Self-Test ===";
  let orig_cov_dir = Sys.getenv_opt "VF_COVERAGE_DIR" in

  (* 1. Exercise a known subset of branches *)
  ignore (test_if true);            (* 'then' covered, 'else' uncovered *)
  ignore (test_match 1);           (* case 1 covered, others uncovered *)
  ignore (test_match 2);           (* case 2 covered, case '_' uncovered *)
  ignore (test_while 2);           (* while loop body covered *)
  ignore (test_for 3);             (* for loop body covered *)
  ignore (test_try false);         (* try body covered, exception case uncovered *)

  (* 2. Test in-process registered modules inspection *)
  let mods = Vf_cov_runtime.get_registered_modules () in
  Printf.printf "Found %d registered module(s) in-process.\n" (List.length mods);
  assert (List.length mods > 0);

  let self_mod =
    List.find (fun (f, _, _) -> Filename.basename f = "cov_self_test.ml") mods
  in
  let (file, points, counters) = self_mod in
  let total_pts = Array.length points in
  Printf.printf "Module %s has %d instrumentation points.\n" file total_pts;
  assert (total_pts >= 10);

  let covered_count = ref 0 in
  let uncovered_count = ref 0 in
  for i = 0 to total_pts - 1 do
    let (l, c, k) = points.(i) in
    let hits = counters.(i) in
    if hits > 0 then incr covered_count else incr uncovered_count;
    Printf.printf "  Point %2d (L%d:C%d, %s): %d hits\n" i l c k hits
  done;
  Printf.printf "In-process summary: %d covered, %d uncovered.\n" !covered_count !uncovered_count;
  assert (!covered_count > 0);
  assert (!uncovered_count > 0);

  (* 3. Test dump_stats to file *)
  let tmp_base = Filename.temp_file "vfcov_test_" "" in
  (try Sys.remove tmp_base with _ -> ());
  Unix.mkdir tmp_base 0o755;
  Unix.putenv "VF_COVERAGE_DIR" tmp_base;

  Vf_cov_runtime.dump_stats ();

  let dumped_files =
    Sys.readdir tmp_base
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".vfcov")
  in
  assert (List.length dumped_files = 1);
  let dump_file = Filename.concat tmp_base (List.hd dumped_files) in
  Printf.printf "Coverage dumped successfully to: %s\n" dump_file;
  assert ((Unix.stat dump_file).Unix.st_size > 0);

  (* 4. Locate and run vf_cov_report *)
  let dir = Filename.dirname Sys.executable_name in
  let candidate1 = Filename.concat dir "vf_cov_report.exe" in
  let candidate2 = Filename.concat dir "vf_cov_report" in
  let report_exe =
    if Sys.file_exists candidate1 then candidate1
    else if Sys.file_exists candidate2 then candidate2
    else failwith (Printf.sprintf "Could not find vf_cov_report in %s" dir)
  in

  let json_path = Filename.concat tmp_base "summary.json" in
  let lcov_path = Filename.concat tmp_base "lcov.info" in
  let md_path = Filename.concat tmp_base "uncovered.md" in

  let cmd =
    Printf.sprintf "%s --cov-dir %s --out-json %s --out-lcov %s --out-md %s"
      (Filename.quote report_exe) (Filename.quote tmp_base)
      (Filename.quote json_path) (Filename.quote lcov_path) (Filename.quote md_path)
  in
  Printf.printf "Running report generator:\n  %s\n" cmd;
  let code = Sys.command cmd in
  assert (code = 0);

  (* 5. Validate generated reports *)
  assert (Sys.file_exists json_path);
  assert (Sys.file_exists lcov_path);
  assert (Sys.file_exists md_path);

  let json_content = read_whole_file json_path in
  let lcov_content = read_whole_file lcov_path in
  let md_content = read_whole_file md_path in

  Printf.printf "JSON report size: %d bytes\n" (String.length json_content);
  Printf.printf "LCOV report size: %d bytes\n" (String.length lcov_content);
  Printf.printf "MD report size:   %d bytes\n" (String.length md_content);

  assert (String.length json_content > 0);
  assert (String.length lcov_content > 0);
  assert (String.length md_content > 0);

  (* JSON assertions *)
  assert (contains_substring "\"total_points\":" json_content);
  assert (contains_substring "\"covered_points\":" json_content);
  assert (contains_substring "\"coverage_pct\":" json_content);
  assert (contains_substring "\"lines_total\":" json_content);
  assert (contains_substring "\"lines_covered\":" json_content);
  assert (contains_substring "\"line_coverage_pct\":" json_content);
  assert (contains_substring "\"branches_total\":" json_content);
  assert (contains_substring "\"branches_covered\":" json_content);
  assert (contains_substring "\"branch_coverage_pct\":" json_content);
  assert (contains_substring "\"functions_total\":" json_content);
  assert (contains_substring "\"functions_covered\":" json_content);
  assert (contains_substring "\"function_coverage_pct\":" json_content);
  assert (contains_substring "cov_self_test.ml" json_content);

  (* LCOV assertions *)
  assert (contains_substring "SF:" lcov_content);
  assert (contains_substring "DA:" lcov_content);
  assert (contains_substring "end_of_record" lcov_content);

  (* MD assertions *)
  assert (contains_substring "cov_self_test.ml" md_content);
  assert (contains_substring "uncovered" md_content);

  (* Clean up isolated test files *)
  let files = Sys.readdir tmp_base in
  Array.iter (fun f -> Sys.remove (Filename.concat tmp_base f)) files;
  Unix.rmdir tmp_base;

  (* Restore original coverage directory and dump for caller suite if applicable *)
  (match orig_cov_dir with
   | Some d when String.trim d <> "" ->
     Unix.putenv "VF_COVERAGE_DIR" d;
     Vf_cov_runtime.dump_stats ()
   | _ -> ());

  print_endline "=== All Coverage Infrastructure Self-Tests Passed! ==="
