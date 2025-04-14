(* Wrapper script passed to 'cargo' using CARGO_BUILD_RUSTC_WRAPPER by 'cargo-verifast' and 'cargo-vfide'.
   Records the arguments in target/verifast-rustc-args.json. *)

open Unix

let () =
  let self_path::rustc_path::args = Array.to_list Sys.argv in
  let rustc_verifast_args, args = List.partition (fun arg -> arg = "--record-rustc-args") args in
  if rustc_verifast_args <> [] then begin
    let source_files, args = List.partition (fun arg -> not (String.starts_with ~prefix:"-" arg) && Filename.check_suffix arg ".rs") args in
    let source_file =
      match source_files with
      | [source_file] -> source_file
      | _ -> failwith "Expected exactly one source file"
    in
    let open Json in
    let rustc_args_json = O [("source_file", S source_file); ("args", A (List.map (fun arg -> S arg) args))] in
    let rustc_args_text = string_of_json rustc_args_json in
    let oc = open_out "target/verifast-rustc-args.json" in
    output_string oc rustc_args_text;
    close_out oc
  end;
  let child = create_process rustc_path (Array.of_list (rustc_path::args)) stdin stdout stderr in
  let _, status = waitpid [] child in
  exit begin match status with
    | WEXITED n -> n
    | WSIGNALED n -> 128 + n
    | WSTOPPED n -> 128 + n
  end
