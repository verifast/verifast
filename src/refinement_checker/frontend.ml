let input_fully c =
  let buf = Bytes.create 60000 in
  let b = Buffer.create 60000 in
  let rec iter () =
    let n = input c buf 0 60000 in
    if n = 0 then Buffer.contents b
    else (
      Buffer.add_subbytes b buf 0 n;
      iter ())
  in
  iter ()

let rec last l =
  match l with [] -> None | lst :: [] -> Some lst | _ :: tl -> last tl

module SysUtil = struct
  let gen_unix_error_msg ecode fname param =
    let emsg = Unix.error_message ecode in
    emsg ^ ". Failed call:" ^ fname ^ "(" ^ param ^ ")"

  let run_command cmd args env =
    try
      let cmd = cmd ^ " " ^ args in
      let output_ic, input_oc, err_ic = Unix.open_process_full cmd env in
      let cmd_output = input_fully output_ic in
      let cmd_err = input_fully err_ic in
      match Unix.close_process_full (output_ic, input_oc, err_ic) with
      | Unix.WEXITED 0 -> cmd_output
      | Unix.WEXITED n ->
          failwith
            (Printf.sprintf "Command '%s' failed with exit code %d: %s" cmd n
               cmd_err)
      | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
          failwith (Printf.sprintf "Command '%s' was killed or stopped" cmd)
    with Unix.Unix_error (ecode, fname, param) ->
      let emsg = gen_unix_error_msg ecode fname param in
      failwith (Printf.sprintf "Could not run command '%s': %s" cmd emsg)
end

module RustTChain = struct
  type tchain_path = Root | Lib

  let find_tchain_path tchain_name tchain_path =
    try
      let rustc_cmd = "rustc" in
      let rustc_args = "+" ^ tchain_name ^ " --print " in
      let rustc_args =
        rustc_args
        ^ match tchain_path with Root -> "sysroot" | Lib -> "target-libdir"
      in
      let current_env = Unix.environment () in
      let tchain_path = SysUtil.run_command rustc_cmd rustc_args current_env in
      let tchain_path = String.trim tchain_path in
      tchain_path
    with Unix.Unix_error (ecode, fname, param) ->
      let emsg = SysUtil.gen_unix_error_msg ecode fname param in
      failwith
        (Printf.sprintf "Could not determine Rust toolchain path: %s" emsg)

  let find_tchain_root tchain_name = find_tchain_path tchain_name Root
  let find_tchain_lib tchain_name = find_tchain_path tchain_name Lib
end

let add_path_to_env_var env var_name path =
  if String.length var_name = 0 then
    failwith "Environment var names should not be empty"
  else
    let env = Array.to_list env in
    let key = var_name ^ "=" in
    let key_len = String.length key in
    let key_uppercase = String.uppercase_ascii key in
    let env, var_values =
      List.partition_map
        (fun entry ->
          let entry_len = String.length entry in
          if entry_len < key_len then Left entry
          else
            let entry_key = String.sub entry 0 key_len in
            let matches =
              match Vfconfig.platform with
              | Windows -> key_uppercase = String.uppercase_ascii entry_key
              | _ -> key = entry_key
            in
            if matches then
              Right (String.sub entry key_len (entry_len - key_len))
            else Left entry)
        env
    in
    let entry = var_name ^ "=" ^ path in
    let entry =
      match last var_values with
      | None -> entry
      | Some value ->
          entry ^ (if Sys.os_type = "Win32" then ";" else ":") ^ value
    in
    let env = env @ [ entry ] in
    Array.of_list env

let run_vf_mir_exporter (rustc_args : string list) (rs_file_path : string) =
  try
    (*** TODO @Nima: Get these names from build system *)
    let tchain_name = "nightly-2025-05-09" in
    let tchain_root = RustTChain.find_tchain_root tchain_name in
    let tchain_lib, rustc_driver_prefix =
      match Vfconfig.platform with
      | Windows -> (tchain_root ^ "/bin", "rustc_driver-")
      | _ -> (tchain_root ^ "/lib", "librustc_driver-")
    in
    let bin_name = "vf-rust-mir-exporter" in
    let bin_dir = Filename.dirname Sys.executable_name in
    let bin_path = bin_dir ^ "/" ^ bin_name in
    if
      not
        (Array.exists
           (String.starts_with ~prefix:rustc_driver_prefix)
           (Sys.readdir tchain_lib))
    then
      failwith
        (Printf.sprintf
           "To verify Rust programs, VeriFast requires the rustc-dev component \
            of the %s Rust toolchain, but this component is currently not \
            installed; please run 'rustup +%s component add rustc-dev' to \
            install it."
           tchain_name tchain_name)
    else
      let args =
        Array.of_list
          ([ bin_path; rs_file_path; "--sysroot=" ^ tchain_root ] @ rustc_args)
      in
      let current_env = Unix.environment () in
      let env =
        add_path_to_env_var current_env
          (match Vfconfig.platform with
          | MacOS -> "DYLD_LIBRARY_PATH"
          | Windows -> "PATH"
          | _ -> "LD_LIBRARY_PATH")
          tchain_lib
      in
      (* Printf.eprintf "Running %s with arguments %s\n" bin_path (String.concat " " (List.map (Printf.sprintf "'%s'") (Array.to_list args)));
         flush stderr; *)
      let chns = Unix.open_process_args_full bin_path args env in
      chns
  with
  | Sys_error emsg ->
      failwith (Printf.sprintf "Could not run vf-rust-mir-exporter: %s" emsg)
  | Unix.Unix_error (ecode, fname, param) ->
      let emsg = SysUtil.gen_unix_error_msg ecode fname param in
      failwith (Printf.sprintf "Could not run vf-rust-mir-exporter: %s" emsg)

let get_vf_mir (rustc_args : string list) (rs_file_path : string) =
  let msg_in_chn, out_chn, err_in_chn =
    run_vf_mir_exporter rustc_args rs_file_path
  in
  let module CpIO = Capnp_unix.IO in
  let msg_rd_ctx =
    CpIO.create_read_context_for_channel ~compression:`None msg_in_chn
  in
  let rec read_vf_mir_exp_msgs msgs =
    match CpIO.ReadContext.read_message msg_rd_ctx with
    | None -> List.rev msgs
    | Some msg_rw -> read_vf_mir_exp_msgs (msg_rw :: msgs)
  in
  let msgs_cell = ref None in
  let emsgs_cell = ref None in
  let msg_rd_job () =
    let msgs = read_vf_mir_exp_msgs [] in
    msgs_cell := Some msgs
  in
  let err_rd_job () =
    let emsgs = input_fully err_in_chn in
    emsgs_cell := Some emsgs
  in
  let msg_rd_th = Thread.create msg_rd_job () in
  let err_rd_th = Thread.create err_rd_job () in
  Thread.join msg_rd_th;
  Thread.join err_rd_th;
  let (Some emsg) = !emsgs_cell in
  try
    (*** TODO @Nima: Can we force to close channels in case of exception *)
    match Unix.close_process_full (msg_in_chn, out_chn, err_in_chn) with
    | Unix.WEXITED 0 ->
        (* print_endline emsgs; *)
        let (Some [ msg ]) = !msgs_cell in
        msg
    | result ->
        let failInfo =
          match result with
          | Unix.WEXITED 1 ->
              (* Rustc aborted due to compilation errors *)
              Printf.printf
                "Could not obtain the MIR because of rustc compilation errors:\n";
              let emsg_lines = String.split_on_char '\n' emsg in
              let diagnostics =
                List.filter
                  (String.starts_with ~prefix:{|{"$message_type":"diagnostic"|})
                  emsg_lines
              in
              let open Json in
              diagnostics
              |> List.iter (fun diagnostic ->
                     let diagnostic = parse_json diagnostic in
                     print_endline (o_assoc "rendered" diagnostic |> s_value));
              exit 1
          | Unix.WEXITED exitCode ->
              let exitCodeInfo =
                match exitCode with
                | -1073741515 when Sys.os_type = "Win32" ->
                    " (Missing DLL; define VERIFAST_DEBUG_MISSING_DLL to see \
                     dialog box with details)"
                | _ -> ""
              in
              Printf.sprintf "exited with exit code %d%s" exitCode exitCodeInfo
          | Unix.WSIGNALED signal ->
              Printf.sprintf "was killed with signal %d" signal
          | Unix.WSTOPPED signal ->
              Printf.sprintf "was stopped with signal %d" signal
        in
        failwith
          (Printf.sprintf "Rust MIR exporter executable %s:\n%s" failInfo emsg)
  with Unix.Unix_error (ecode, fname, param) ->
    let emsg = SysUtil.gen_unix_error_msg ecode fname param in
    failwith (Printf.sprintf "Could not run vf-rust-mir-exporter: %s" emsg)
