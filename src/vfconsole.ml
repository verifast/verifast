open Verifast

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify stats options prover path =
    let streamSource path =
      Stream.of_string (readFile path)
    in
    try
      verify_program prover stats options path (streamSource path) streamSource (fun _ -> ()) (fun _ -> ()) None;
      print_endline "0 errors found"
    with
      ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg)); exit 1
    | StaticError (l, msg) -> print_msg l msg; exit 1
    | SymbolicExecutionError (ctxts, phi, l, msg) ->
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        (*
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_endline ("Failed query: " ^ phi) in
        let _ = print_msg l msg in
        exit 1
  in
  let n = Array.length Sys.argv in
  if n = 1 then
  begin
    print_endline Verifast.banner;
    print_endline "Usage: verifast [-stats] [-verbose] [-disable_overflow_check] [-prover z3|redux] [-c] [-shared] [-allow_assume] {sourcefile|objectfile}"
  end
  else
  let stats = ref false in
  let verbose = ref false in
  let disable_overflow_check = ref false in
  let prover: string option ref = ref None in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let modules: string list ref = ref [] in
  let i = ref 1 in
  while !i < n do
    let arg = Sys.argv.(!i) in
    i := !i + 1;
    if String.length arg > 0 && String.get arg 0 = '-' then
      match arg with
        "-stats" -> stats := true
      | "-verbose" -> verbose := true
      | "-disable_overflow_check" -> disable_overflow_check := true
      | "-prover" -> prover := Some Sys.argv.(!i); i := !i + 1
      | "-c" -> compileOnly := true
      | "-shared" -> isLibrary := true
      | "-allow_assume" -> allowAssume := true
      | _ -> failwith ("unknown command-line option '" ^ arg ^ "'")
    else
    begin
      if Filename.check_suffix arg ".c" || Filename.check_suffix arg ".java" || Filename.check_suffix arg ".jarsrc"
	  then
      begin
        print_endline arg;
        verify !stats {option_verbose = !verbose; option_disable_overflow_check = !disable_overflow_check} !prover arg
      end;
      modules := arg::!modules
    end
  done;
  if not !compileOnly then
  begin
    try
      print_endline "Linking...";
      let mydir = Filename.dirname Sys.executable_name in
      let crt = Filename.concat mydir "crt.a" in
      let assume_lib = Filename.concat mydir "assume.a" in
      let modules = crt::List.rev !modules in
      let modules = if !allowAssume then assume_lib::modules else modules in
      link_program (!isLibrary) modules; 
      print_endline "Program linked successfully."
    with
      LinkError msg -> print_endline msg; exit 1
  end
