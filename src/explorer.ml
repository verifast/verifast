open Arg
open Parser
open Verifast1
open Ast
open Lexer
open Util

(* TODOs:
  - make the data_model a command line argument
*)

let _ =

  let is_first_arg = ref true in
  let pattern_str = ref "" in
  let files_to_explore: string list ref = ref [] in

  let process_args (arg: string): unit =
    if (!is_first_arg) then
      (is_first_arg := false ; pattern_str := arg)
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
  Printf.printf "Pattern is %s and number of files to explore is %d.\n" !pattern_str (List.length !files_to_explore);
  if (not (check_args_valid ()) ) then (Printf.printf "Program exiting\n" ; exit 1);
  
  (* Callbacks *)
  let sourceFiles : (string * (((int * int) * (int * int)) * range_kind) list ref) list ref = ref [] in
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

  let parse_c_file (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: loc0 -> unit) (verbose: int) 
          (include_paths: string list) (define_macros: string list) (enforceAnnotations: bool) (dataModel: data_model) (parsePattern: bool): ((loc * (include_kind * string * string) * string list * package list) list * package list) = (* ?parse_c_file *)
    let result =
      let make_lexer path include_paths ~inGhostRange =
        let text = 
          if (parsePattern) then 
            "/*@ lemma void dummy_function() requires true ; ensures " ^ !pattern_str ^ "; {} @*/"
          else
            readFile path
        in
        make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange reportShouldFail
      in
      let (loc, token_stream) = make_preprocessor make_lexer path verbose include_paths dataModel define_macros in
      let parse_c_file =
        parser
          [< (headers, _) = parse_include_directives verbose enforceAnnotations dataModel; 
                              ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:false; '(_, Eof) >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
      in
      try
        parse_c_file token_stream
      with
        Stream.Error msg -> raise (ParseException (loc(), msg))
      | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
    in
    result
  in

  let extract_postcond _ : expr =
    let (_, package_list) = parse_c_file "dummy.c" reportRange reportShouldFail 0 [] [] true data_model_32bit true in
    match package_list with
      | pack_head :: _ -> 
        begin
          match pack_head with 
            | PackageDecl(_, _, _, declarations) -> 
              begin
                match declarations with
                  | decl_head :: _ -> 
                    begin
                      match decl_head with
                        | Func(_, _, _, _, _, _, _, _, contract_opt, _, _, _, _) -> 
                          begin 
                            match contract_opt with
                              | Some contract -> 
                                let (_, postcond) = contract in 
                                postcond
                          end
                    end
              end

        end
  in

  let pattern_expr = extract_postcond () in

  let check_file_for_pattern (filepath: string): unit =
    
    let rec check_expr_for_pattern (expr: expr) (pattern: expr) : bool = 
      match expr with
        | True(_) -> (match pattern with True(_) -> true | _ -> false)
        | False(_) -> (match pattern with False(_) -> true | _ -> false)
        | Null(_) -> (match pattern with Null(_) -> true | _ -> false)
        | Var(_) -> (match pattern with Var(_) -> true | _ -> false)
        | Operation(_, operator, operands) ->
          begin
            let pattern_in_operands = List.fold_left (fun acc op -> acc || (check_expr_for_pattern op pattern)) false operands in
            match pattern with
              | Operation(_, pattern_operator, pattern_operands) -> 
                begin
                  let each_operand_same : bool = 
                    if (operator = pattern_operator && List.length operands = List.length pattern_operands) then
                      List.fold_left (fun acc (expr_op, pattern_op) -> acc && (check_expr_for_pattern expr_op pattern_op)) true (zip2 operands pattern_operands)
                    else
                      false
                  in
                  each_operand_same || pattern_in_operands
                end
              | _ -> pattern_in_operands
          end
        | CallExpr(_, name, types, _, args, _) -> (* supports only LitPat and DummyPat as arguments in expr and pattern*)
          begin
            let filter_func x = match x with | LitPat(_) -> true | _ -> false in
            let map_func x = match x with | LitPat(ex) -> ex | _ -> Null(DummyLoc) in (* default case cannot happen because of filter *)
            let filter_args = List.filter filter_func args in
            let map_filter_args = List.map map_func filter_args in
            let pattern_in_args = List.fold_left (fun acc arg -> acc || (check_expr_for_pattern arg pattern)) false map_filter_args in
            match pattern with
              | CallExpr(_, pattern_name, pattern_types, _, pattern_args, _) ->
                begin
                  let each_arg_same : bool =
                    let ziped_args = zip2 args pattern_args in
                    let rec dummy_in_expr_not_in_pattern (ziped_args: (pat * pat) list) : bool = 
                      (* returns false if at least one argument of expr is a dummy and the corresponding one in the pattern is not *)
                      match ziped_args with
                        | [] -> true
                        | (DummyPat, pattern_arg) :: _ when pattern_arg <> DummyPat -> false
                        | head :: tail -> dummy_in_expr_not_in_pattern tail
                    in
                    if (dummy_in_expr_not_in_pattern ziped_args && name = pattern_name && List.length args = List.length pattern_args) then (* check that types are the same ?*)
                      let rec eliminate_dummy_in_pattern (ziped_args: (pat * pat) list) : (pat * pat) list =
                        match ziped_args with
                          | [] -> []
                          | (_, DummyPat) :: tail -> eliminate_dummy_in_pattern tail
                          | head :: tail -> head :: (eliminate_dummy_in_pattern tail)
                      in
                      let rec extract_expr (ziped_args: (pat * pat) list) : (expr * expr) list =
                        match ziped_args with
                          | (LitPat(x), LitPat(y)) :: tail -> (x, y) :: (extract_expr tail)
                          | _ :: tail -> (Null(DummyLoc), Null(DummyLoc)) :: (extract_expr tail) (* default case cannot happen because of previous filtering *)
                      in
                      List.fold_left (fun acc (expr_arg, pattern_arg) -> acc && (check_expr_for_pattern expr_arg pattern_arg)) false (extract_expr (eliminate_dummy_in_pattern ziped_args))
                    else
                      false
                  in
                  each_arg_same || pattern_in_args
                end
              | _ -> pattern_in_args
          end
        | Sep(_, lhs, rhs) -> (check_expr_for_pattern lhs pattern) || (check_expr_for_pattern rhs pattern)
        | _ -> false;
    in

    let rec check_declarations (declaration_list: decl list): unit = 
      match declaration_list with
        | [] -> ();
        | decl_head :: decl_tail -> 
          begin
            let () = 
              match decl_head with
                | Func(_, _, type_parameters, return_type, name, parameters, _, _, contract_opt, _, _, _, _) -> 
                  begin 
                    match contract_opt with
                      | None -> Printf.printf "Function %s has no contract.\n" name;
                      | Some contract -> 
                        let (_, postcond) = contract in 
                        let res = check_expr_for_pattern postcond pattern_expr in
                        Printf.printf "Checking postcondition of function %s -> %B\n" name res;
                  end
                | _ -> Printf.printf "\tNot a function\n";
            in 
            check_declarations decl_tail;
          end
    in

    let rec check_packages (package_list: package list): unit =
      match package_list with
        | [] -> ();
        | pack_head :: pack_tail -> 
          begin
            let () = match pack_head with | PackageDecl(_, _, _, declarations) -> check_declarations declarations in
            check_packages pack_tail;
          end
    in

    let (_, package_list) = parse_c_file filepath reportRange reportShouldFail 0 [] [] true data_model_32bit false in
    let () = check_packages package_list in
    Printf.printf "Parsed %s\n" filepath
  in

  let _  = parse_c_file "fake.c" reportRange reportShouldFail 0 [] [] true data_model_32bit true in
  List.iter check_file_for_pattern !files_to_explore
    
(*  *)