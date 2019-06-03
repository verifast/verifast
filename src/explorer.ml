open Arg
open Parser
open Verifast1
open Ast
open Lexer

(* TODOs:
  - make the data_model a command line argument
*)

let _ =

  let is_first_arg = ref true in
  let pattern = ref "" in
  let files_to_explore: string list ref = ref [] in

  let process_args (arg: string): unit =
    if (!is_first_arg) then
      (is_first_arg := false ; pattern := arg)
    else
      files_to_explore := arg :: !files_to_explore
  in

  let check_args_valid _ : bool =
      if (!is_first_arg) then (Printf.printf "No pattern or empty pattern specified\n");
      if (List.length !files_to_explore = 0) then (Printf.printf "No file to explore specified\n");
      not !is_first_arg && (List.length !files_to_explore) <> 0
  in

  (* Parse command-line arguments and check that a pattern and at least one file to explore were provided *)
  parse [] process_args "Failed to parse command-line arguments.";
  Printf.printf "Pattern is %s and number of files to explore is %d.\n" !pattern (List.length !files_to_explore);
  if (not (check_args_valid ()) ) then (Printf.printf "Program exiting\n" ; exit 1);

  let sourceFiles : (string * (((int * int) * (int * int)) * range_kind) list ref) list ref = ref [] in
  
  (* Callbacks *)
  let reportRange kind ((path1, line1, col1), (path2, line2, col2)) =    
    assert (path1 = path2);
    let path = path1 in
    let ranges =
      if List.mem_assoc path !sourceFiles then
        List.assoc path !sourceFiles
      else
      begin
        let ranges : (((int * int) * (int * int)) * range_kind) list ref = ref [] in
        sourceFiles := (path, ranges)::!sourceFiles;
        ranges
      end
    in
    ranges := (((line1, col1), (line2, col2)), kind)::!ranges
  in

  let shouldFailLocs: loc0 list ref = ref [] in
  let reportShouldFail l = shouldFailLocs := l::!shouldFailLocs in

  let check_in_file (filepath: string): unit =
    let res_parse = parse_c_file filepath reportRange reportShouldFail 0 [] [] true data_model_32bit in
    Printf.printf "Parsed %s\n" filepath
  in

  List.iter check_in_file !files_to_explore
    
