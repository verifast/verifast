module VfMirTr = Vf_mir_translator
module VfMirStub = VfMirTr.VfMirStub
module VfMirRd = VfMirTr.VfMirRd

exception RustFrontend of string

let ( let* ) = Result.bind

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
      let* tchain_path = SysUtil.run_command rustc_cmd rustc_args current_env in
      let tchain_path = String.trim tchain_path in
      Ok tchain_path
    with Unix.Unix_error (ecode, fname, param) ->
      let emsg = SysUtil.gen_unix_error_msg ecode fname param in
      Error (`SysCallFailed emsg)

  let find_tchain_root tchain_name = find_tchain_path tchain_name Root

  let find_tchain_lib tchain_name = find_tchain_path tchain_name Lib
end

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
    let env = Array.append [| "LD_LIBRARY_PATH=" ^ tchain_lib |] current_env in
    let chns = Unix.open_process_args_full bin_path args env in
    Ok chns
  with
  | Sys_error emsg -> Error (`SysCallFailed emsg)
  | Unix.Unix_error (ecode, fname, param) ->
      let emsg = SysUtil.gen_unix_error_msg ecode fname param in
      Error (`SysCallFailed emsg)

(*** If we use several messages later, it would work more efficient than storing everything and then deserializing it *)
let get_vf_mir_rd (rs_file_path : string) =
  let* msg_in_chn, out_chn, err_in_chn = run_vf_mir_exporter rs_file_path in
  let module CpIO = Capnp_unix.IO in
  let rd_ctx =
    CpIO.create_read_context_for_channel ~compression:`None msg_in_chn
  in
  let rec read_vf_mir_exp_msgs msgs =
    try
      match CpIO.ReadContext.read_message rd_ctx with
      | None -> Ok msgs
      | Some msg_rw -> read_vf_mir_exp_msgs (msgs @ [ msg_rw ])
    with CpIO.Unsupported_message_frame ->
      Error (`CapnpMsgReadingFailed "Unsupported message frame")
  in
  let close_chns () =
    try
      (*** TODO @Nima: Can we force to close channels in case of exception *)
      let emsg = Util.input_fully err_in_chn in
      match Unix.close_process_full (msg_in_chn, out_chn, err_in_chn) with
      | Unix.WEXITED 0 -> Ok ()
      | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
          Error (`RustMirExpFailed emsg)
    with Unix.Unix_error (ecode, fname, param) ->
      let emsg = SysUtil.gen_unix_error_msg ecode fname param in
      Error (`SysCallFailed emsg)
  in
  let* msgs = read_vf_mir_exp_msgs [] in
  let* _ = close_chns () in
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
        | `RustMirExpFailed emsg ->
            "Rust MIR exporter executable failed: " ^ emsg
        | `SysCallFailed emsg -> "System call failed: " ^ emsg
      in
      raise (RustFrontend (gen_emsg ^ desc))
