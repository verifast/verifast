module type RUST_FE_ARGS = sig
  val data_model_opt : Ast.data_model option
  val report_should_fail : string -> Ast.loc0 -> unit
  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
  val report_macro_call : Ast.loc0 -> Ast.loc0 -> unit
end

module Make (Args : RUST_FE_ARGS) = struct
  open Ocaml_aux
  module VfMirTr = Vf_mir_translator.Make (Args)
  module VfMirRd = VfMirTr.VfMirRd

  exception RustFrontend of string

  module SysUtil = struct
    let gen_unix_error_msg ecode fname param =
      let emsg = Unix.error_message ecode in
      emsg ^ ". Failed call:" ^ fname ^ "(" ^ param ^ ")"

    let run_command cmd args env =
      try
        let cmd = cmd ^ " " ^ args in
        let output_ic, input_oc, err_ic = Unix.open_process_full cmd env in
        let cmd_output = Util.input_fully output_ic in
        let cmd_err = Util.input_fully err_ic in
        match Unix.close_process_full (output_ic, input_oc, err_ic) with
        | Unix.WEXITED 0 -> Ok cmd_output
        | Unix.WEXITED _ -> Error (`CmdFailed (cmd, cmd_err))
        | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> Error (`ProcessFailed cmd)
      with Unix.Unix_error (ecode, fname, param) ->
        let emsg = gen_unix_error_msg ecode fname param in
        Error (`SysCallFailed emsg)
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
        let* tchain_path =
          SysUtil.run_command rustc_cmd rustc_args current_env
        in
        let tchain_path = String.trim tchain_path in
        Ok tchain_path
      with Unix.Unix_error (ecode, fname, param) ->
        let emsg = SysUtil.gen_unix_error_msg ecode fname param in
        Error (`SysCallFailed emsg)

    let find_tchain_root tchain_name = find_tchain_path tchain_name Root
    let find_tchain_lib tchain_name = find_tchain_path tchain_name Lib
  end

  let add_path_to_env_var env var_name path =
    if String.length var_name = 0 then
      Error (`EnvSettingFailed "Environment var names should not be empty")
    else
      let env = Array.to_list env in
      let env, var_values =
        List.partition_map
          (fun entry ->
            let key = var_name ^ "=" in
            if String.starts_with ~prefix:key entry then
              let entry_len, key_len =
                (String.length entry, String.length key)
              in
              Right (String.sub entry key_len (entry_len - key_len))
            else Left entry)
          env
      in
      let entry = var_name ^ "=" ^ path in
      let entry =
        match ListAux.last var_values with
        | None -> entry
        | Some value -> entry ^ ":" ^ value
      in
      let env = env @ [ entry ] in
      Ok (Array.of_list env)

  let run_vf_mir_exporter (rs_file_path : string) =
    try
      (*** TODO @Nima: Get these names from build system *)
      let tchain_name = "nightly-2022-01-31" in
      let bin_name = "vf-rust-mir-exporter" in
      let bin_dir = Filename.dirname Sys.executable_name in
      let bin_path = bin_dir ^ "/" ^ bin_name in
      let* tchain_root = RustTChain.find_tchain_root tchain_name in
      let* tchain_lib = RustTChain.find_tchain_lib tchain_name in
      let args = [| bin_path; rs_file_path; "--sysroot=" ^ tchain_root |] in
      let current_env = Unix.environment () in
      let* env = add_path_to_env_var current_env (match Vfconfig.platform with MacOS -> "DYLD_LIBRARY_PATH" | _ -> "LD_LIBRARY_PATH") tchain_lib in
      let chns = Unix.open_process_args_full bin_path args env in
      Ok chns
    with
    | Sys_error emsg -> Error (`SysCallFailed emsg)
    | Unix.Unix_error (ecode, fname, param) ->
        let emsg = SysUtil.gen_unix_error_msg ecode fname param in
        Error (`SysCallFailed emsg)

  let get_vf_mir_rd (rs_file_path : string) =
    let* msg_in_chn, out_chn, err_in_chn = run_vf_mir_exporter rs_file_path in
    let module CpIO = Capnp_unix.IO in
    let msg_rd_ctx =
      CpIO.create_read_context_for_channel ~compression:`None msg_in_chn
    in
    let rec read_vf_mir_exp_msgs msgs =
      try
        match CpIO.ReadContext.read_message msg_rd_ctx with
        | None -> Ok msgs
        | Some msg_rw -> read_vf_mir_exp_msgs (msgs @ [ msg_rw ])
      with
      | CpIO.Unsupported_message_frame ->
          Error (`CapnpMsgReadingFailed "Unsupported message frame")
      | _ -> Error (`CapnpMsgReadingFailed "Unsupported exception")
    in
    let rd_ths_res = ref ((*msg reader*) None, (*err reader*) None) in
    let rd_ths_mtx = Mutex.create () in
    let rd_ths_cond = Condition.create () in
    let msg_rd_job _ =
      let res = read_vf_mir_exp_msgs [] in
      Mutex.lock rd_ths_mtx;
      (match res with
      | Ok msgs -> rd_ths_res := (Some (Ok msgs), snd !rd_ths_res)
      | Error err -> rd_ths_res := (Some (Error err), snd !rd_ths_res));
      Condition.broadcast rd_ths_cond;
      Mutex.unlock rd_ths_mtx
    in
    let err_rd_job _ =
      let emsgs =
        try Ok (Util.input_fully err_in_chn)
        with _ -> Error (`ErrMsgReadingFailed "Unsupported exception")
      in
      Mutex.lock rd_ths_mtx;
      (match emsgs with
      | Ok emsgs -> rd_ths_res := (fst !rd_ths_res, Some (Ok emsgs))
      | Error emsg -> rd_ths_res := (fst !rd_ths_res, Some (Error emsg)));
      Condition.broadcast rd_ths_cond;
      Mutex.unlock rd_ths_mtx
    in
    let run_jobs _ =
      let msg_rd_th = Thread.create msg_rd_job () in
      let err_rd_th = Thread.create err_rd_job () in
      Mutex.lock rd_ths_mtx;
      while
        match !rd_ths_res with
        | Some (Error _), _ | _, Some (Error _) -> false
        | Some (Ok _), Some (Ok _) -> false
        | _ -> true
      do
        Condition.wait rd_ths_cond rd_ths_mtx
      done;
      let res =
        match !rd_ths_res with
        | Some (Ok msgs), Some (Ok emsgs) -> Ok (msgs, emsgs)
        | Some (Error err), _ | _, Some (Error err) -> Error err
        | _ -> failwith "Should not happen"
      in
      Mutex.unlock rd_ths_mtx;
      res
    in
    let close_chns emsgs =
      try
        (*** TODO @Nima: Can we force to close channels in case of exception *)
        match Unix.close_process_full (msg_in_chn, out_chn, err_in_chn) with
        | Unix.WEXITED 0 -> Ok ()
        | result ->
            Error (`RustMirExpFailed (result, emsgs))
      with Unix.Unix_error (ecode, fname, param) ->
        let emsg = SysUtil.gen_unix_error_msg ecode fname param in
        Error (`SysCallFailed emsg)
    in
    let* msgs =
      match run_jobs () with
      | Ok (msgs, emsgs) ->
          let* _ = close_chns emsgs in
          Ok msgs
      | Error err ->
          let* _ = close_chns "No error message could be read from std_err" in
          Error err
    in
    match msgs with
    | [] -> Error (`RustMirDesFailed "No message from Rust MIR exporter")
    (*** For now we are just using the first message *)
    | msg :: _ -> (
        try
          let vf_mir_rd = VfMirRd.of_message msg in
          Ok vf_mir_rd
        with Capnp.Message.Invalid_message emsg ->
          Error
            (`RustMirDesFailed
              ("Cannot create VF MIR from the received message. " ^ emsg)))

  let parse_rs_file (rs_file_path : string) =
    match get_vf_mir_rd rs_file_path with
    | Ok vf_mir_rd -> VfMirTr.translate_vf_mir vf_mir_rd
    | Error einfo ->
        let gen_emsg = "Rust frontend failed to generate VF MIR: " in
        let desc =
          match einfo with
          | `CmdFailed (cmd, emsg) ->
              "System Command [" ^ cmd ^ "] failed. Error:" ^ emsg
          | `ProcessFailed bin ->
              "Process for [" ^ bin ^ "] is been signaled or stopped"
          | `RustMirDesFailed emsg ->
              "Capnp message deserialization failed: " ^ emsg
          | `RustMirExpFailed (result, emsg) ->
              let failInfo =
                match result with
                  Unix.WEXITED exitCode ->
                  let exitCodeInfo =
                    match exitCode with
                      -1073741515 when Sys.os_type = "Win32" -> " (Missing DLL; define VERIFAST_DEBUG_MISSING_DLL to see dialog box with details)"
                    | _ -> ""
                  in
                  Printf.sprintf "exited with exit code %d%s" exitCode exitCodeInfo
                | Unix.WSIGNALED signal -> Printf.sprintf "was killed with signal %d" signal
                | Unix.WSTOPPED signal -> Printf.sprintf "was stopped with signal %d" signal
              in
              Printf.sprintf "Rust MIR exporter executable %s: %s" failInfo emsg
          | `SysCallFailed emsg -> "System call failed: " ^ emsg
        in
        raise (RustFrontend (gen_emsg ^ desc))
end
