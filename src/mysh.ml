let parse_cmdline line =
  try
    let space = String.index line ' ' in
    [String.sub line 0 space; String.sub line (space + 1) (String.length line - space - 1)]
  with Not_found -> [line]

let rec exec_lines lineno =
  try
    let line = read_line () in
    let n = String.length line in
    let line = if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line in
    print_endline line;
    begin
      match parse_cmdline line with
        ["cd"; dir] -> Sys.chdir dir
      | ["del"; file] -> Sys.remove file
      | _ ->
        let status = Sys.command line in
        print_newline ();
        if status <> 0 then
          failwith ("mysh: line " ^ string_of_int lineno ^ ": exit code " ^ string_of_int status)
    end;
    exec_lines (lineno + 1)
  with End_of_file -> ()

let () = exec_lines 1
