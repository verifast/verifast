let parse_cmdline line =
  try
    let space = String.index line ' ' in
    [String.sub line 0 space; String.sub line (space + 1) (String.length line - space - 1)]
  with Not_found -> [line]

let read_line_canon file =
  let line = input_line file in
  let n = String.length line in
  if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line

let macros = ref []

let rec exec_lines filepath file lineno =
  let error msg =
    failwith (Printf.sprintf "mysh: %s: line %d: %s" filepath lineno msg)
  in
  try
    let line = read_line_canon file in
    let rec exec_line line =
      print_endline line;
      match parse_cmdline line with
        ["cd"; dir] -> Sys.chdir dir
      | ["del"; file] -> Sys.remove file
      | ["let"; macroName] ->
        let lines =
          let rec read_macro_lines () =
            let line = read_line_canon file in
            if line = "in" then [] else line::read_macro_lines ()
          in
          read_macro_lines ()
        in
        macros := (macroName, lines)::!macros
      | ["include"; includepath] ->
        let file = try open_in includepath with Sys_error s -> error (Printf.sprintf "Could not open include file '%s': %s" includepath s) in
        exec_lines includepath file 1;
        close_in file
      | [cmdName; args] when List.mem_assoc cmdName !macros ->
        List.iter (fun line -> exec_line (Printf.sprintf "%s %s" line args)) (List.assoc cmdName !macros)
      | _ ->
        let time0 = Unix.gettimeofday() in
        let status = Sys.command line in
        let time1 = Unix.gettimeofday() in
        Printf.printf "%f seconds\n" (time1 -. time0);
        print_newline ();
        if status <> 0 then
          error (Printf.sprintf "exit code %d" status)
    in
    exec_line line;
    exec_lines filepath file (lineno + 1)
  with End_of_file -> ()

let () = exec_lines "standard input" stdin 1
