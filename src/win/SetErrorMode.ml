external set_error_mode: unit -> unit = "caml_SetErrorMode"

let () =
  if Sys.getenv_opt "VERIFAST_DEBUG_MISSING_DLL" = None then
    set_error_mode ()
