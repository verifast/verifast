open Ast
open Lexer
open Parser
open Util
open Arg

type explore_result = (loc * string) 
type lemma = (loc * string * asn)
type mapping = (string * expr)

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

  (* let parse_header_file_custom (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: loc0 -> unit) (verbose: int) 
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
  in *)

  (* My code *)

  let file_filter (filename: string): bool =
    Filename.check_suffix filename ".c" || Filename.check_suffix filename ".h" || Filename.check_suffix filename ".gh"
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

  let rec get_decls_from_filepaths (filepaths: string list) (include_paths: string list) (define_macros: string list): (decl list) list =
    match filepaths with
      | [] -> []
      | filepath :: tail ->
        let fail_msg (path: string) (msg: string) : unit = Printf.printf("[FILE IGNORED] Parsing of file %s failed with message: %s.\n") path msg in
        if (Filename.check_suffix filepath ".gh" || Filename.check_suffix filepath ".h") then
              let packages = 
                try
                  let (_, packages_tmp) = parse_header_file filepath reportRange reportShouldFail 0 include_paths define_macros false data_model_32bit in
                  packages_tmp
                with
                  Lexer.ParseException(_, msg) -> let _ = fail_msg filepath msg in []
              in
              match packages with
                | [] -> get_decls_from_filepaths tail include_paths define_macros
                | pack_head :: pack_tail -> 
                    match pack_head with | PackageDecl(_, _, _, declarations) -> declarations :: (get_decls_from_filepaths tail include_paths define_macros)
        else if (Filename.check_suffix filepath ".c") then
            let packages = 
                try
                  let (_, packages_tmp) = parse_c_file filepath reportRange reportShouldFail 0 include_paths define_macros false data_model_32bit in
                  packages_tmp
                with
                  Lexer.ParseException(_, msg) -> let _ = fail_msg filepath msg in []
            in
            match packages with
              | [] -> get_decls_from_filepaths tail include_paths define_macros
              | pack_head :: pack_tail -> 
                  match pack_head with | PackageDecl(_, _, _, declarations) -> declarations :: (get_decls_from_filepaths tail include_paths define_macros)
        else (* Should never happen. If it does, simply ignore the file *)
          get_decls_from_filepaths tail include_paths define_macros
  in

  let rec get_lemmas_from_decls (decls_to_explore: (decl list) list): lemma list =
    
    let rec parse_decl_list (declaration_list: decl list): lemma list = 
    match declaration_list with
      | [] -> []
      | head :: tail -> 
        match head with
          | Func(loc, _, _, _, name, _, _, _, contract_opt, _, _, _, _) -> 
            begin 
              match contract_opt with
                | None -> parse_decl_list tail
                | Some contract -> let (_, postcond) = contract in (loc, name, postcond) :: parse_decl_list tail
            end
          | FuncTypeDecl(loc, _, _, name, _, _, _, (_, postcond, _)) -> (loc, name, postcond) :: parse_decl_list tail
          | _ -> parse_decl_list tail
    in

    match decls_to_explore with
      | [] -> []
      | head :: tail -> List.append (parse_decl_list head) (get_lemmas_from_decls tail)
  in
    
  let pattern_str_to_expr (pattern_str: string) : expr =
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

  (* Second return value is true if this is a binary operation, false either. Third return value true when binary operation is symmetric *)
  let operator_info (op: operator) : string * bool * bool =
    match op with
    | Add -> "+", true, true
    | Sub -> "-", true, false
    | PtrDiff -> "p-", true, false
    | Le -> "<=", true, false
    | Ge -> ">=", true, false
    | Lt -> "<", true, false
    | Gt -> ">", true, false
    | Eq -> "==", true, true
    | Neq -> "!=", true, true
    | And -> "&&", true, true
    | Or -> "||", true, true
    | Xor -> "^^", true, true
    | Not -> "!", false, false
    | Mul -> "*", true, true
    | Div -> "/", true, false
    | Mod -> "%%", true, false
    | BitNot -> "~", false, false
    | BitAnd -> "&", false, false
    | BitXor -> "^", false, false
    | BitOr -> "|", false, false
    | ShiftLeft -> "<<", true, false
    | ShiftRight-> ">>", true, false
  in

  let are_operators_opposite (op: operator) (other_op: operator) : bool =
    match op with
      | Le -> (match other_op with Ge -> true | _ -> false)
      | Ge -> (match other_op with Le -> true | _ -> false)
      | Lt -> (match other_op with Gt -> true | _ -> false)
      | Gt -> (match other_op with Lt -> true | _ -> false)
      | _ -> false
  in

  let rec string_of_expr (expr: expr) : string =

    let rec string_of_pat (pat: pat) : string =
      match pat with
        | LitPat(expr) -> string_of_expr expr
        | VarPat(_, varname) ->"?Var_" ^ varname
        | DummyPat -> "_"
        | CtorPat(_, name, pat_list) -> "Ctor_" ^ name ^ "(" ^ string_of_pat_list pat_list ^ " )"
    and string_of_pat_list (pat_list: pat list) : string =
      match pat_list with
        | [] -> ""
        | head :: [] -> string_of_pat head
        | head :: tail -> (string_of_pat head) ^ ", " ^ (string_of_pat_list tail)
    in

    let rec string_of_expr_list (expr_list: expr list) : string =
      match expr_list with
        | [] -> ""
        | head :: [] -> string_of_expr head
        | head :: tail -> (string_of_expr head) ^ ", " ^ (string_of_expr_list tail)
    in

    let rec string_of_switch (switch: switch_asn_clause) : string =
      match switch with
        | SwitchAsnClause(_, name, _, expr_in) -> "case " ^ name ^ ": " ^ string_of_expr expr_in
    and string_of_switch_list (switch_list: switch_asn_clause list) : string =
      match switch_list with
        | [] -> ""
        | head :: [] -> string_of_switch head
        | head :: tail -> (string_of_switch head) ^ ", " ^ (string_of_switch_list tail)
    in

    let rec string_of_type_expr (type_expr: type_expr) : string =
      match type_expr with
        | StructTypeExpr(_, name_opt, _) -> (match name_opt with Some name -> name | _ -> "")
        | EnumTypeExpr(_, name_opt, _) -> (match name_opt with Some name -> name | _ -> "")
        | PtrTypeExpr(_, type_expr_in) -> string_of_type_expr type_expr_in ^ "*"
        | ArrayTypeExpr(_, type_expr_in) -> string_of_type_expr type_expr_in ^ "[]"
        | StaticArrayTypeExpr(_, type_expr_in, nb_elems) -> string_of_type_expr type_expr_in ^ "[" ^ string_of_int nb_elems ^ "]"
        | ManifestTypeExpr(_) -> "manifest"
        | IdentTypeExpr(_, _, name) -> name
        | ConstructedTypeExpr(_, name, type_expr_list) -> name ^ "<" ^ string_of_type_expr_list type_expr_list ^ ">"
        | PredTypeExpr(_, type_expr_list, _) -> string_of_type_expr_list type_expr_list
        | PureFuncTypeExpr(_, type_expr_list) -> string_of_type_expr_list type_expr_list
    and string_of_type_expr_list (type_expr_list: type_expr list) : string =
      match type_expr_list with
        | [] -> ""
        | head :: [] -> string_of_type_expr head
        | head :: tail -> (string_of_type_expr head) ^ ", " ^ (string_of_type_expr_list tail)
    in

    match expr with 
      | True(_) -> "True"
      | False(_) -> "False"
      | Null(_) -> "Null"
      | Var(_, varname) -> "Var_" ^ varname
      | TruncatingExpr(_, expr_in) -> "Truncating(" ^ string_of_expr expr_in ^ ")"
      | Operation(_, operator, operands) -> 
        let (op_str, isBinary, _) = operator_info operator in
        if (isBinary) then
          string_of_expr (List.nth operands 0) ^ " " ^ op_str ^ " " ^ string_of_expr (List.nth operands 1)
        else
          " " ^ op_str ^ string_of_expr (List.nth operands 0)
      | IntLit(_, integer, _, _, _) -> Big_int.string_of_big_int integer
      | RealLit(_, real) -> Num.string_of_num real
      | StringLit(_, str) -> "\"" ^ str ^ "\""
      | Read(_, expr_in, str) -> string_of_expr expr_in ^ "." ^ str
      | ArrayLengthExpr(_, expr_in) -> "ArrayLength " ^ string_of_expr expr_in ^ ")"
      | ReadArray(_, array_expr, index_expr) -> string_of_expr array_expr ^ "[" ^ string_of_expr index_expr ^ "]" 
      | Deref(_, expr_in) -> "*" ^ string_of_expr expr_in
      | CallExpr(_, name, _, _, args, _) -> name ^ "(" ^ string_of_pat_list args ^ ")"
      | ExprCallExpr(_, callee_expr, args_expr) -> string_of_expr callee_expr ^ "(" ^ string_of_expr_list args_expr ^ ")"
      | IfExpr(_, cond_expr, then_expr, else_expr) -> "if (" ^ string_of_expr cond_expr ^ ") then {" ^ string_of_expr then_expr ^ "} else {" ^ string_of_expr else_expr ^ "}"
      | CastExpr(_, type_cast, expr_in) -> "(" ^ string_of_type_expr type_cast ^ ")" ^ string_of_expr expr_in 
      | SizeofExpr(_, type_sizeof) -> "sizeof(" ^ string_of_type_expr type_sizeof ^ ")"
      | AddressOf(_, expr_in) -> "&" ^ string_of_expr expr_in
      | AssignExpr(_, rec_expr, val_expr) -> "(" ^ string_of_expr rec_expr ^ " = " ^ string_of_expr val_expr ^ ")"
      | PointsTo(_, expr_in, pat) -> "PointsTo(" ^ string_of_expr expr_in ^ ", " ^ string_of_pat pat ^ ")"
      | ExprAsn(_, expr_in) -> string_of_expr expr_in
      | Sep(_, lhs, rhs) -> (string_of_expr lhs) ^ " &*& " ^ (string_of_expr rhs)
      | IfAsn(_, cond_expr, then_expr, else_expr) -> "if (" ^ string_of_expr cond_expr ^ ") then {" ^ string_of_expr then_expr ^ "} else {" ^ string_of_expr else_expr ^ "}"
      | SwitchAsn(_, switch_expr, clauses) -> "switch(" ^ string_of_expr switch_expr ^ ") {" ^ string_of_switch_list clauses ^ "}"
      | EmpAsn(_) -> "emp" 
      | CoefAsn(_, perm, expr_in) -> "[" ^ string_of_pat perm ^ "]" ^ string_of_expr expr_in 
      | _ -> "unknown"
  in

  let rec check_expr_for_pattern (expr: expr) (pattern: expr) (exactMacthOnly: bool) : bool * (mapping list) list) = 

    let check_expr_list_for_pattern (expr_list: expr list) (pattern: expr) : bool * ((mapping list) list) =
      match expr_list with
        | [] -> false, []
        | head :: tail -> 
          let (res, mappings) = check_expr_for_pattern head pattern false in
          let (tail_res, tail_mappings) = check_expr_list_for_pattern tail pattern in
          if (res) then true, List.append mappings tail_mappings else tail_res, tail_mappings
    in

    let check_expr_list_for_pattern_list (expr_list: expr list) (pattern_list: expr list) : bool =
      match expr_list with 
        | [] -> true, []
        | head :: tail ->
          begin
            match pattern_list with
              | pattern_head :: pattern_tail ->
                let (res, mappings) = check_expr_for_pattern head pattern_head true in
                let (tail_res, tail_mappings) = check_expr_list_for_pattern_list tail pattern_tail true in
                (* hypothesis: mappings and tail_mappings have at most length 1 *)
                if (res && tail_res) then true, [ List.append (List.nth mappings 0) (List.nth tail_mappings 0) ] else false, []
          end
    in

    let rec check_pat_list_for_pattern (pat_list: pat list) (pattern: expr): bool = List.fold_left (fun acc pat_in -> acc || (check_pat_for_pattern pat_in pattern)) false pat_list
    and check_pat_for_pattern (pat: pat) (pattern: expr) : bool =
      match pat with 
        | LitPat(expr) -> check_expr_for_pattern expr pattern false
        | VarPat(_) -> false
        | DummyPat -> false
        | CtorPat(_, _, pat_list) -> check_pat_list_for_pattern pat_list pattern
    in

    let rec check_pat_equal (pat: pat) (pattern_pat: pat): bool =
      let fold_check_pat_equal (pat_list: pat list) (pattern_pat_list: pat list): bool = 
        if (List.length pat_list = List.length pattern_pat_list) then
          List.fold_left (fun acc (pat_in, pattern_pat_in) -> acc && (check_pat_equal pat_in pattern_pat_in)) true (zip2 pat_list pattern_pat_list)
        else false
      in
      match (pat, pattern_pat) with 
        | _, DummyPat -> true (* if the pattern is a dummy, we don't care about the type of this expression*)
        | LitPat(expr), LitPat(pattern_expr) -> check_expr_for_pattern expr pattern_expr true
        | VarPat(_), VarPat(_) -> true
        | CtorPat(_, name, pat_list), CtorPat(_, pattern_name, pattern_pat_list) when name = pattern_name -> fold_check_pat_equal pat_list pattern_pat_list
        | LitPat(expr), CtorPat(_, pattern_name, pattern_pat_list) -> 
          begin
            match expr with
              | CallExpr(_, name, _, _, args, _) when name = pattern_name -> fold_check_pat_equal args pattern_pat_list
              | _ -> false (* TODO: Add support for predicates ?*)
          end
    in

    let rec check_type_equal (type_: type_) (pattern_type_: type_): bool =
      match type_ with
        | Bool -> (match pattern_type_ with Bool -> true | _ -> false)
        | Void -> (match pattern_type_ with Void -> true | _ -> false)
        | Int(signed, rank) -> (match pattern_type_ with Int(pattern_signed, pattern_rank) when signed = pattern_signed && rank = pattern_rank -> true | _ -> false)
        | RealType -> (match pattern_type_ with RealType -> true | _ -> false)
        | Float -> (match pattern_type_ with Float -> true | _ -> false)
        | Double -> (match pattern_type_ with Double -> true | _ -> false)
        | LongDouble -> (match pattern_type_ with LongDouble -> true | _ -> false)
        | StructType(name) -> (match pattern_type_ with StructType(pattern_name) when name = pattern_name -> true | _ -> false)
        | PtrType(type_in) -> (match pattern_type_ with PtrType(pattern_type_in) -> check_type_equal type_in pattern_type_in | _ -> false)
        | FuncType(name) -> (match pattern_type_ with FuncType(pattern_name) when name = pattern_name -> true | _ -> false)
        | InductiveType(name, type_list)  -> (match pattern_type_ with InductiveType(pattern_name, pattern_type_list) when name = pattern_name -> check_type_equal_list type_list pattern_type_list | _ -> false)
        | PredType(names, type_list, _, inductive) ->
          begin
            match pattern_type_ with
              | PredType(pattern_names, pattern_type_list, _, pattern_inductive) when inductive = pattern_inductive ->
                check_type_equal_list type_list pattern_type_list && check_name_equal_list names pattern_names
              | _ -> false
          end
        | PureFuncType(type_in1, type_in2) -> (match pattern_type_ with PureFuncType(pattern_type_in1, pattern_type_in2) -> check_type_equal type_in1 pattern_type_in1 && check_type_equal type_in2 pattern_type_in2 | _ -> false)
        | ObjType(name) -> (match pattern_type_ with ObjType(pattern_name) when name = pattern_name -> true | _ -> false) 
        | ArrayType(type_in) -> (match pattern_type_ with ArrayType(pattern_type_in) -> check_type_equal type_in pattern_type_in | _ -> false)
        | StaticArrayType(type_in, size) -> (match pattern_type_ with StaticArrayType(pattern_type_in, pattern_size) when size = pattern_size -> check_type_equal type_in pattern_type_in | _ -> false)
        | BoxIdType -> (match pattern_type_ with BoxIdType -> true | _ -> false)
        | HandleIdType -> (match pattern_type_ with HandleIdType -> true | _ -> false)
        | AnyType -> (match pattern_type_ with AnyType -> true | _ -> false)
        | TypeParam(name) -> (match pattern_type_ with TypeParam(pattern_name) when name = pattern_name -> true | _ -> false) 
        | ClassOrInterfaceName(name) -> (match pattern_type_ with ClassOrInterfaceName(pattern_name) when name = pattern_name -> true | _ -> false) 
        | PackageName(name) -> (match pattern_type_ with PackageName(pattern_name) when name = pattern_name -> true | _ -> false) 
        | RefType(type_in) -> (match pattern_type_ with RefType(pattern_type_in) -> check_type_equal type_in pattern_type_in | _ -> false)
        | AbstractType(name) -> (match pattern_type_ with AbstractType(pattern_name) when name = pattern_name -> true | _ -> false) 
    and check_type_equal_list (type_list: type_ list) (pattern_type_list: type_ list) : bool =
      List.fold_left (fun acc (type_, pattern_type_) -> acc && check_type_equal type_ pattern_type_) true (zip2 type_list pattern_type_list) 
    and check_name_equal_list (names: string list) (pattern_names: string list) : bool =
      List.fold_left (fun acc (name, pattern_name) -> acc && name = pattern_name) true (zip2 names pattern_names) 
    in

    let rec check_type_expr_equal (type_expr: type_expr) (pattern_type_expr: type_expr): bool =
      match type_expr with
        | StructTypeExpr(_, name_opt, _) -> 
          begin
            match pattern_type_expr with
              | StructTypeExpr(_, pattern_name_opt, _) ->
                begin
                  match name_opt with
                    | Some name -> (match pattern_name_opt with Some(pattern_name) when name = pattern_name -> true | None -> false) 
                    | None -> true
                end
              | _ -> false
          end
        | EnumTypeExpr(_, name_opt, _) ->
           begin
            match pattern_type_expr with
              | EnumTypeExpr(_, pattern_name_opt, _) ->
                begin
                  match name_opt with
                    | Some name -> (match pattern_name_opt with Some(pattern_name) when name = pattern_name -> true | None -> false) 
                    | None -> true
                end
              | _ -> false
          end
        | PtrTypeExpr(_, type_expr_in) ->
          begin
            match pattern_type_expr with
              | PtrTypeExpr(_, pattern_type_expr_in) -> check_type_expr_equal type_expr_in pattern_type_expr_in
              | _ -> false
          end
        | ArrayTypeExpr(_, type_expr_in) ->
          begin
            match pattern_type_expr with
              | ArrayTypeExpr(_, pattern_type_expr_in) -> check_type_expr_equal type_expr_in pattern_type_expr_in
              | _ -> false
          end
        | StaticArrayTypeExpr(_, type_expr_in, nb_elems) ->
          begin
            match pattern_type_expr with
              | StaticArrayTypeExpr(_, pattern_type_expr_in, pattern_nb_elems) when nb_elems = pattern_nb_elems -> check_type_expr_equal type_expr_in pattern_type_expr_in
              | _ -> false
          end
        | ManifestTypeExpr(_, type_) ->
          begin
            match pattern_type_expr with
              | ManifestTypeExpr(_, pattern_type_) -> check_type_equal type_ pattern_type_
              | _ -> false
          end
        | IdentTypeExpr(_, _, name) ->
          begin
            match pattern_type_expr with
              | IdentTypeExpr(_, _, pattern_name) when name = pattern_name -> true
              | _ -> false
          end
        | ConstructedTypeExpr(_, name, type_expr_list) ->
          begin
             match pattern_type_expr with
              | ConstructedTypeExpr(_, pattern_name, pattern_type_expr_list) when name = pattern_name -> check_type_expr_equal_list type_expr_list pattern_type_expr_list
              | _ -> false
          end
        | PredTypeExpr(_, type_expr_list, _) ->
          begin
             match pattern_type_expr with
              | PredTypeExpr(_, pattern_type_expr_list, _) -> check_type_expr_equal_list type_expr_list pattern_type_expr_list
              | _ -> false
          end
        | PureFuncTypeExpr(_, type_expr_list) ->
          begin
             match pattern_type_expr with
              | PureFuncTypeExpr(_, pattern_type_expr_list) -> check_type_expr_equal_list type_expr_list pattern_type_expr_list
              | _ -> false
          end
    and check_type_expr_equal_list (type_expr_list: type_expr list) (pattern_type_expr_list: type_expr list) : bool =
      List.fold_left (fun acc (type_expr, pattern_type_expr) -> acc && check_type_expr_equal type_expr pattern_type_expr) true (zip2 type_expr_list pattern_type_expr_list) 
    in

    let check_if_then_else (if_terms: expr list) : bool =
      let pattern_inside = if (exactMacthOnly) then false else check_expr_list_for_pattern if_terms pattern in
      match pattern with
        | IfAsn(_, pattern_cond_expr, pattern_then_expr, pattern_else_expr) ->
          let pattern_if_terms = [pattern_cond_expr; pattern_then_expr; pattern_else_expr] in pattern_inside || check_expr_list_for_pattern_list if_terms pattern_if_terms
        | IfExpr(_, pattern_cond_expr, pattern_then_expr, pattern_else_expr) ->
          let pattern_if_terms = [pattern_cond_expr; pattern_then_expr; pattern_else_expr] in pattern_inside || check_expr_list_for_pattern_list if_terms pattern_if_terms
        | _ -> false
    in

    match pattern with
      | Var(_, varname) -> true [ [(varname, expr)] ]
      | _ ->
        begin
          match expr with
            | True(_) -> (match pattern with True(_) -> true | _ -> false)
            | False(_) -> (match pattern with False(_) -> true | _ -> false)
            | Null(_) -> (match pattern with Null(_) -> true | _ -> false)
            | Var(_) -> (match pattern with Var(_) -> true | _ -> false)
            | TruncatingExpr(_, expr_in) ->
              let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
              begin
                match pattern with
                  | TruncatingExpr(_, pattern_expr_in) -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside 
                  | _ -> pattern_inside
              end
            | Operation(_, operator, operands) ->
              begin
                let pattern_in_operands = if (exactMacthOnly) then false else check_expr_list_for_pattern operands pattern in
                match pattern with
                  | Operation(_, pattern_operator, pattern_operands) when List.length operands = List.length pattern_operands -> 
                    begin
                      let switch_operands_same = if (List.length operands < 2) then false
                        else check_expr_for_pattern (List.nth operands 0) (List.nth pattern_operands 1) true || check_expr_for_pattern (List.nth operands 1) (List.nth pattern_operands 0) true 
                      in
                      let operands_same = check_expr_list_for_pattern_list operands pattern_operands in

                      let all_operands_match = 
                        if (operator = pattern_operator) then 
                          let (_, isBinary, isSymmetric) = operator_info operator in
                          if (isBinary && isSymmetric) then
                            switch_operands_same || operands_same
                          else
                            operands_same
                        else if (are_operators_opposite operator pattern_operator) then
                          switch_operands_same
                        else
                          false
                      in
                      pattern_in_operands || all_operands_match
                    end
                  | _ -> pattern_in_operands
              end
            | IntLit(_, integer, _, _, _) -> 
              begin
                match pattern with 
                  | IntLit(_, pattern_integer, _, _, _) when (Big_int.compare_big_int integer pattern_integer) = 0 -> true
                  | _ -> false
              end
            | RealLit(_, real) ->
              begin
                match pattern with
                  | RealLit(_, pattern_real) when Num.eq_num real pattern_real -> true
                  | _ -> false
              end
            | StringLit(_, str) ->
              begin
                match pattern with
                  | StringLit(_, pattern_str) when str = pattern_str -> true
                  | _ -> false
              end
            | Read(_, expr_in, str) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | Read(_, pattern_expr_in, pattern_str) when str = pattern_str -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside 
                  | _ -> pattern_inside
              end
            | ArrayLengthExpr(_, expr_in) -> 
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | ArrayLengthExpr(_, pattern_expr_in) -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside
                  | _ -> pattern_inside
              end
            | ReadArray(_, array_expr, index_expr) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else (check_expr_for_pattern array_expr pattern false) || (check_expr_for_pattern index_expr pattern false) in
                match pattern with
                    | ReadArray(_, pattern_array_expr, pattern_index_expr) -> 
                      pattern_inside || (check_expr_for_pattern array_expr pattern_array_expr true && check_expr_for_pattern index_expr pattern_index_expr true)
                    | _ -> pattern_inside
              end
            | Deref(_, expr_in) -> 
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | Deref(_, pattern_expr_in) -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside 
                  | _ -> pattern_inside
              end
            | CallExpr(_, name, _, _, args, _) ->
              begin
                let pattern_in_args = if (exactMacthOnly) then false else check_pat_list_for_pattern args pattern in
                match pattern with
                  | CallExpr(_, pattern_name, _, _, pattern_args, _) when name = pattern_name && List.length args = List.length pattern_args ->
                    begin
                      let each_arg_same = List.fold_left (fun acc (arg, pattern_arg) -> acc && check_pat_equal arg pattern_arg) true (zip2 args pattern_args) in
                      each_arg_same || pattern_in_args
                    end
                  | _ -> pattern_in_args
              
              end
            | ExprCallExpr(_, callee_expr, args_expr) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false 
                  else check_expr_for_pattern callee_expr pattern false || check_expr_list_for_pattern args_expr pattern
                in
                match pattern with
                  | ExprCallExpr(_, pattern_callee_expr, pattern_args_expr) -> 
                    pattern_inside || (check_expr_for_pattern callee_expr pattern_callee_expr true && check_expr_list_for_pattern_list args_expr pattern_args_expr)
                  | _ -> pattern_inside
              end
            | IfExpr(_, cond_expr, then_expr, else_expr) -> check_if_then_else [cond_expr; then_expr; else_expr]
            | CastExpr(_, type_cast, expr_in) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with 
                  | CastExpr(_, pattern_type_cast, pattern_expr_in) -> 
                    pattern_inside || (check_type_expr_equal type_cast pattern_type_cast && check_expr_for_pattern expr_in pattern_expr_in true) 
                  | _ -> pattern_inside
              end
            | SizeofExpr(_, type_sizeof) -> (match pattern with SizeofExpr(_, pattern_type_sizeof) -> check_type_expr_equal type_sizeof pattern_type_sizeof | _ -> false)
            | AddressOf(_, expr_in) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | AddressOf(_, pattern_expr_in) -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside
                  | _ -> pattern_inside 
              end
            | AssignExpr(_, rec_expr, val_expr) -> 
              begin
                let pattern_inside = if (exactMacthOnly) then false else (check_expr_for_pattern rec_expr pattern false) || (check_expr_for_pattern val_expr pattern false) in
                match pattern with
                    | AssignExpr(_, pattern_rec_expr, pattern_val_expr) -> 
                      pattern_inside || (check_expr_for_pattern rec_expr pattern_rec_expr true && check_expr_for_pattern val_expr pattern_val_expr true)
                    | _ -> pattern_inside
              end
            | PointsTo(_, expr_in, pat) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false || check_pat_for_pattern pat pattern in
                match pattern with
                  | PointsTo(_, pattern_expr_in, pattern_pat) -> pattern_inside || (check_expr_for_pattern expr_in pattern_expr_in true && check_pat_equal pat pattern_pat) 
                  | _ -> pattern_inside 
              end
            | ExprAsn(_, expr_in) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | ExprAsn(_, pattern_expr_in) -> check_expr_for_pattern expr_in pattern_expr_in true || pattern_inside
                  | _ -> pattern_inside 
              end
            | Sep(_, lhs, rhs) -> 
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_expr_for_pattern lhs pattern false || check_expr_for_pattern rhs pattern false in
                match pattern with
                  | Sep(_, pattern_lhs, pattern_rhs) ->
                    pattern_inside || (check_expr_for_pattern lhs pattern_lhs true && check_expr_for_pattern rhs pattern_rhs true)
                  | _ -> pattern_inside
              end
            | IfAsn(_, cond_expr, then_expr, else_expr) -> check_if_then_else [cond_expr; then_expr; else_expr]
            | SwitchAsn(_, switch_expr, clauses) -> 
              begin
                let rec extract_expr_from_clauses (clauses: switch_asn_clause list) : expr list =
                  match clauses with
                    | [] -> []
                    | clause :: tail -> (match clause with SwitchAsnClause(_, _, _, expr_in) -> expr_in :: extract_expr_from_clauses tail)
                in
                let pattern_inside = if (exactMacthOnly) then false 
                  else check_expr_for_pattern switch_expr pattern false || check_expr_list_for_pattern (extract_expr_from_clauses clauses) pattern 
                in
                match pattern with
                  | SwitchAsn(_, pattern_switch_expr, pattern_clauses) when List.length clauses = List.length pattern_clauses -> 
                    let clause_same_str (clause: switch_asn_clause)  (pattern_clause: switch_asn_clause) : bool =
                      match clause with 
                        | SwitchAsnClause(_, name, strs, _) ->
                          begin
                            match pattern_clause with 
                              | SwitchAsnClause(_, pattern_name, pattern_strs, _) when name = pattern_name && List.length strs = List.length pattern_strs -> 
                                  List.fold_left (fun acc (str, pattern_str) -> acc && str = pattern_str) true (zip2 strs pattern_strs)
                              | _ -> false
                          end
                    in
                    pattern_inside || (List.fold_left (fun acc (clause, pattern_clause) -> acc && clause_same_str clause pattern_clause) true (zip2 clauses pattern_clauses) && 
                      check_expr_list_for_pattern_list (extract_expr_from_clauses clauses) (extract_expr_from_clauses pattern_clauses))
                  | _ -> pattern_inside
              end
            | EmpAsn(_) -> (match pattern with EmpAsn(_) -> true | _ -> false)
            | CoefAsn(_, perm, expr_in) ->
              begin
                let pattern_inside = if (exactMacthOnly) then false else check_pat_for_pattern perm pattern || check_expr_for_pattern expr_in pattern false in
                match pattern with
                  | CoefAsn(_, pattern_perm, pattern_expr_in) -> pattern_inside || (check_pat_equal perm pattern_perm && check_expr_for_pattern expr_in pattern_expr_in true)
                  | _ -> pattern_inside
              end
            | _ -> false;
        end
  in

  let rec search_for_pattern (lemmas: lemma list) (pattern: expr): unit =

    let filename_from_loc (loc: loc): string =
      match loc with
        | Lexed(loc0) -> let ((p1, _, _), _) = loc0 in " in file " ^ p1
        | _ -> ""
    in

    let print_explore_result ((loc, name): explore_result): unit =
      let startline_from_loc (loc: loc): string =
        match loc with
          | Lexed(loc0) -> let ((_, l1, _), _) = loc0 in "At line " ^ string_of_int l1 ^ ": "
          | _ -> ""
      in  
      Printf.printf("\t%sPost-condition of lemma %s()\n") (startline_from_loc loc) name
    in

    match lemmas with 
      | [] -> ()
      | (loc, name, postcond) :: tail ->
        let _ =
          if (check_expr_for_pattern postcond pattern false) then
            Printf.printf("Match %s\n") name
          else
            ()
        in
        search_for_pattern tail pattern
  in

  let remove_duplicate_lemmas (lemmas: lemma list) ((loc, name, postcond): lemma): bool =
    let filename_from_loc (loc: loc): string =
      match loc with
        | Lexed(((p1, _, _), _)) -> p1
        | _ -> ""
    in
    if (Filename.check_suffix (filename_from_loc loc) ".c") then
      let rec check_for_duplicate (lemmas_in: lemma list) : bool =
        match lemmas_in with
          | [] -> true
          | (loc_in, name_in, postcond_in) :: tail -> 
            if (Filename.check_suffix (filename_from_loc loc_in) ".gh" && name = name_in && check_expr_for_pattern postcond postcond_in true) then
              false
            else 
              check_for_duplicate tail
      in
      check_for_duplicate lemmas
    else
      true
  in

  let include_paths: string list ref = ref [] in
  let define_macros: string list ref = ref [] in
  let explore_paths: string list ref = ref [] in

  (* CLA syntax definition *)
  let cla = [ "-I", String (fun str -> include_paths := str :: !include_paths), "Add a directory to the list of directories to be searched for header files." 
            ; "-D", String (fun str -> define_macros := str :: !define_macros), "Predefine name as a macro, with definition 1."
            ]
  in

  (* Parse command-line arguments *)
  parse cla (fun str -> explore_paths := str :: !explore_paths) "Failed to parse command-line arguments.";

  let files_to_explore = get_files_from_explore_paths (!explore_paths) in
  let decls_to_explore = get_decls_from_filepaths files_to_explore !include_paths !define_macros in
  let lemmas_to_explore = get_lemmas_from_decls decls_to_explore in
  let lemmas_filtered = List.filter (remove_duplicate_lemmas lemmas_to_explore) lemmas_to_explore in
  let _ = Printf.printf "\n== %d lemmas were parsed and will be searched for a pattern ==\n" (List.length lemmas_filtered) in
  let _ = List.iter (fun (_, name, postcond) -> Printf.printf "%s(): %s\n" name (string_of_expr postcond)) lemmas_filtered in

  (* Execution loop *)
  while true do
    Printf.printf "\nEnter a pattern > ";
    let pattern_str = read_line () in
    let pattern_expr_opt = 
      if (pattern_str = "") then
        let _ = Printf.printf "Empty pattern.\n" in
        None
      else
        try
          Some (pattern_str_to_expr pattern_str)
        with
          Lexer.ParseException(_, msg) -> 
            let _ = Printf.printf "Invalid pattern.\n" in
            None
    in
    match pattern_expr_opt with 
      | Some(pattern_expr) -> let _ = Printf.printf "%s\n" (string_of_expr pattern_expr) in search_for_pattern lemmas_filtered pattern_expr
      | None -> ()
  done
