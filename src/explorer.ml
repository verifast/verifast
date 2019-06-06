open Ast
open Lexer
open Parser
open Util
open Arg

(* TODOs:
  - make the data_model a command line argument
*)

let files_blacklist = ["threading.c"]
let verifast_explore_path = "/home/lucas/VeriFast/verifast/bin"

let _ =

  (* Callbacks for parser *)
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

  (* Parsers *)
  let parse_c_file_custom (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: loc0 -> unit) (verbose: int) 
        (include_paths: string list) (define_macros: string list) (enforceAnnotations: bool) (dataModel: data_model) (pattern_str: string): ((loc * (include_kind * string * string) * string list * package list) list * package list) = (* ?parse_c_file_custom *)
    let result =
      let make_lexer path include_paths ~inGhostRange =
        let text = 
          if (pattern_str <> "") then 
            "/*@ lemma void dummy_function() requires true ; ensures " ^ pattern_str ^ "; {} @*/"
          else
            readFile path
        in
        make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange reportShouldFail
      in
      let (loc, token_stream) = make_preprocessor make_lexer path verbose include_paths dataModel define_macros in
      let p =
        parser
          [< (headers, _) = parse_include_directives verbose enforceAnnotations dataModel; 
                              ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:false; '(_, Eof) >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
      in
      try
        p token_stream
      with
        Stream.Error msg -> raise (ParseException (loc(), msg))
      | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
    in
    result
  in

  let parse_header_file_custom (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: loc0 -> unit) (verbose: int) 
          (include_paths: string list) (define_macros: string list) (enforceAnnotations: bool) (dataModel: data_model): ((loc * (include_kind * string * string) * string list * package list) list * package list) =
    let isGhostHeader = Filename.check_suffix path ".gh" in
    let result =
      let make_lexer path include_paths ~inGhostRange =
        let text = readFile path in
        make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange:inGhostRange reportShouldFail
      in
      let (loc, token_stream) = make_preprocessor make_lexer path verbose include_paths dataModel define_macros in
      let p = parser
        [< (headers, _) = parse_include_directives verbose enforceAnnotations dataModel; 
          ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:isGhostHeader; 
          '(_, Eof)
        >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
      in
      try
        p token_stream
      with
        Stream.Error msg -> raise (ParseException (loc(), msg))
      | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
    in
    result
  in

  (* My code *)

  let is_first_arg = ref true in
  let pattern_str = ref "" in
  let include_paths: string list ref = ref [] in
  let explore_paths: string list ref = ref [] in

  let cla = [ "-I", String (fun str -> include_paths := str :: !include_paths), "Add a directory to the list of directories to be searched for header files." ] in

  (* Parse command-line arguments *)
  parse cla (fun str -> explore_paths := str :: !explore_paths) "Failed to parse command-line arguments.";
  Printf.printf "%d directories will be explored.\n" ((List.length !explore_paths) + 1);
  Printf.printf "%d directories will be included.\n" (List.length !include_paths);

  let file_filter (filename: string): bool =
    (Filename.check_suffix filename ".c" || Filename.check_suffix filename ".h" || Filename.check_suffix filename ".gh") && not (List.mem filename files_blacklist)
  in

  let rec get_files_from_explore_paths (explore_paths: string list): string list =
    match explore_paths with
      | [] -> []
      | explore_path :: tail -> 
        let list_files = Array.to_list (Sys.readdir explore_path) in
        let filter_files = List.filter file_filter list_files in
        let absolute_files = List.map (fun str -> explore_path ^ "/" ^ str) filter_files in
        List.append absolute_files (get_files_from_explore_paths tail)
  in

  let rec get_decl_from_filepaths (filepaths: string list): (decl list) list =
    match filepaths with
      | [] -> []
      | filepath :: tail ->
        (* let _ = Printf.printf "%s\n" filepath in *)
        if (Filename.check_suffix filepath ".gh" || Filename.check_suffix filepath ".h") then
              let packages = 
                try
                  let (_, packages_tmp) = parse_header_file filepath reportRange reportShouldFail 0 !include_paths [] false data_model_32bit in
                  packages_tmp
                with
                  Lexer.ParseException(_, msg) -> 
                    let _ = Printf.printf("Parsing of file %s failed with message: %s. The file will be ignored.\n") filepath msg in
                    []
              in
              match packages with
                | [] -> get_decl_from_filepaths tail
                | pack_head :: pack_tail -> 
                    match pack_head with | PackageDecl(_, _, _, declarations) -> declarations :: (get_decl_from_filepaths tail)
        else if (Filename.check_suffix filepath ".c") then
            let packages = 
                try
                  let (_, packages_tmp) = parse_c_file filepath reportRange reportShouldFail 0 !include_paths [] false data_model_32bit in
                  packages_tmp
                with
                  Lexer.ParseException(_, msg) -> 
                    let _ = Printf.printf("Parsing of file %s failed with message: %s. The file will be ignored.\n") filepath msg in
                    []
            in
            match packages with
              | [] -> []
              | pack_head :: pack_tail -> 
                  match pack_head with | PackageDecl(_, _, _, declarations) -> declarations :: (get_decl_from_filepaths tail)
        else (* Should never happen. If it does, simply ignore the file *)
          get_decl_from_filepaths tail
  in

  (* Also add the VeriFast library path to the include paths *)
  let files_to_explore = get_files_from_explore_paths (verifast_explore_path :: !explore_paths) in
  let decls_to_explore = get_decl_from_filepaths files_to_explore in
  (* List.iter (fun str -> Printf.printf "%s\n" str) files_to_explore; *)


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
                      let res = check_expr_for_pattern postcond (Null(DummyLoc)) in
                      Printf.printf "Checking postcondition of function %s -> %B\n" name res;
                end
              | _ -> Printf.printf "\tNot a function\n";
          in 
          check_declarations decl_tail;
        end
  in

  let extract_postcond (pattern_str: string) : expr =
    let (_, package_list) = parse_c_file_custom "dummy.c" reportRange reportShouldFail 0 [] [] true data_model_32bit pattern_str in
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

  (* let (_, package_list) = parse_c_file_custom filepath reportRange reportShouldFail 0 [] [] true data_model_32bit "" in
    let () = check_packages package_list in *)

  Printf.printf "-- Stop\n";