let result = ref 0

type location = Location of string * int

let contains_tab (s : string) : bool =
  String.contains s '\t'  

let find_tabs_in_file (filename : string) (callback : location -> unit) : unit =
  let file =
    open_in filename
  in
  let rec scan line_number =
    let line = input_line file in
    begin
      if contains_tab line
      then callback (Location (filename, line_number))
    end;
    scan (line_number + 1)
  in
  try
    scan 1
  with
      End_of_file -> close_in file

let show_lines_with_tabs (filename : string) : unit =
  let callback (Location (filename, linenumber)) =
    Printf.printf "Found tab in %s on line %d\n" filename linenumber;
    result := !result + 1
  in
  find_tabs_in_file filename callback

let scan_files_with_extension extension =
  let scan filename =
    if Filename.check_suffix filename extension
    then show_lines_with_tabs filename
  in
  let filenames = Sys.readdir "." in
  Array.iter scan filenames


let () =
  scan_files_with_extension ".ml";
  if !result <> 0 then begin
    Printf.printf "Found %d tab(s)\n" !result;
    exit 1
  end
    
