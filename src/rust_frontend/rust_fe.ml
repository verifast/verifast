module VfMirTr = Vf_mir_translator
module VfMirStub = VfMirTr.VfMirStub
module VfMirRd = VfMirTr.VfMirRd

exception RustFrontend of string

let ( let* ) = Result.bind

let gen_unix_error_msg ecode fname param =
  let emsg = Unix.error_message ecode in
  emsg ^ ". Failed call:" ^ fname ^ "(" ^ param ^ ")"

let run_vf_mir_exporter (rs_file_path : string) =
  try
    let bin_name = "vf-rust-mir-exporter" in
    (*** TODO @Nima: Get this name from build system *)
    let bin_dir = Filename.dirname Sys.executable_name in
    let bin_path = bin_dir ^ "/" ^ bin_name in
    let chns =
      Unix.open_process_args_full (*prog*) bin_path
        (*args*) [| rs_file_path |]
        (*env*) [||]
    in
    Ok chns
  with
  | Sys_error emsg -> Error (`SysCallFailed emsg)
  | Unix.Unix_error (ecode, fname, param) ->
      let emsg = gen_unix_error_msg ecode fname param in
      Error (`SysCallFailed emsg)

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
      Error (`CapnpMsgReading "Invalid message frame")
  in
  let close_chns () =
    try
      match Unix.close_process_full (msg_in_chn, out_chn, err_in_chn) with
      | Unix.WEXITED 0 -> Ok ()
      | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
          (*** TODO @Nima: read the err_in_chn content *)
          Error (`RustMirExpFailed "Rust MIR exporter exited unsuccessfully")
    with Unix.Unix_error (ecode, fname, param) ->
      let emsg = gen_unix_error_msg ecode fname param in
      Error (`SysCallFailed emsg)
  in
  let* msgs = read_vf_mir_exp_msgs [] in
  let* _ = close_chns () in
  match msgs with
  (*** TODO @Nima: Check the err_in_chn for possible error messages *)
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
        | `RustMirDesFailed emsg ->
            "Capnp message deserialization failed: " ^ emsg
        | `RustMirExpFailed emsg ->
            "Rust MIR exporter executable failed: " ^ emsg
        | `SysCallFailed emsg -> "System call failed: " ^ emsg
      in
      raise (RustFrontend (gen_emsg ^ desc))
