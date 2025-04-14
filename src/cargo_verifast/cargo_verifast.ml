(*

Source code for the bin/cargo-verifast executable which is called by 'cargo'
when invoked as 'cargo verifast'. First determines the rustc arguments by
invoking 'cargo rustc -- --record-rustc-args' with CARGO_BUILD_RUSTC_WRAPPER set
to 'rustc-verifast', then invokes 'verifast' with the arguments wrapped in
'-rustc_arg' options. 'rustc-verifast' stores the arguments in a file
'target/verifast-rustc-args.json', which 'cargo-verifast' reads.

*)

open Unix

let () =
  let self_path::cmd::args = Array.to_list Sys.argv in
  let cargo_path = getenv "CARGO" in
  let cargo_env = Array.of_list ("CARGO_BUILD_RUSTC_WRAPPER=rustc-verifast"::(Array.to_list (Unix.environment ()))) in
  let child = create_process_env cargo_path [| cargo_path; "rustc"; "--"; "--record-rustc-args" |] cargo_env stdin stdout stderr in
  let _, status = waitpid [] child in
  begin match status with
    | WEXITED 0 -> ()
    | WEXITED n -> exit n
    | WSIGNALED n -> exit (128 + n)
    | WSTOPPED n -> exit (128 + n)
  end;
  let source_file, rustc_args =
    let rustc_args_file = "target/verifast-rustc-args.json" in
    let rustc_args_file_text =
      let ic = open_in rustc_args_file in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      s
    in
    let open Json in
    let rustc_args_json = parse_json rustc_args_file_text in
    let source_file = o_assoc "source_file" rustc_args_json |> s_value in
    let args = o_assoc "args" rustc_args_json |> a_value |> List.map s_value in
    source_file, args
  in
  let verifast_args = args @ (List.map (fun arg -> ["-rustc_arg"; arg]) ("--vf-rust-mir-exporter:no-default-args"::rustc_args) |> List.flatten) @ [source_file] in
  let verifast_args =
    match cmd with
      "verifast" -> "verifast"::"-read_options_from_source_file"::verifast_args
    | "vfide" -> "vfide"::verifast_args
  in
  (* Printf.eprintf "Calling '%s' with arguments %s\n" cmd (String.concat " " (List.map Filename.quote verifast_args));
  flush Stdlib.stderr; *)
  let child = create_process cmd (Array.of_list verifast_args) stdin stdout stderr in
  let _, status = waitpid [] child in
  exit begin match status with
    | WEXITED n -> n
    | WSIGNALED n -> 128 + n
    | WSTOPPED n -> 128 + n
  end