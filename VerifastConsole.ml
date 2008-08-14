open Verifast

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify verbose prover path =
    try
      let channel = open_in path in
      let stream = Stream.of_channel channel in
      verify_program prover verbose path stream (fun _ -> ()) (fun _ -> ());
      print_endline "0 errors found";
      exit 0
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
        let _ = print_endline ("Failed query: " ^ simp phi) in
        let _ = print_msg l msg in
        exit 1
  in
  let n = Array.length Sys.argv in
  if n = 1 then
  begin
    print_endline "Verifast 1.0 for C";
    print_endline "Usage: verifast [-verbose] [-prover (z3|simplify)] filepath"
  end
  else
  let rec iter verbose prover i =
    if i < n then
      let arg = Sys.argv.(i) in
      if String.length arg > 0 && String.get arg 0 = '-' then
        match arg with
          "-verbose" -> iter true prover (i + 1)
        | "-prover" ->
          if i + 1 < n then
            iter verbose (Sys.argv.(i + 1)) (i + 2)
          else
            failwith "-prover option requires argument"
        | _ -> failwith "unknown command-line option '" ^ arg ^ "'"
      else
        if i + 1 = n then
          verify verbose prover arg
        else
          failwith "bad command line"
    else
      failwith "no path specified"
  in
  iter false "z3" 1; ()
