open Ast
open Lexer
open Parser
open Util
open Arg

(* Custom types *)
type explore_result = (loc * string) 
type lemma = (loc * string * asn)
type mapping = (string * expr)
let usage_msg = "\nUsage: explorer [options] {source directories}\n"

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

  (* Custom parser *)
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

  (* 
    Returns the list of files with extensions .h, .c, or .gh from a list of directories. 
    Raises Sys_error if one of the explore_paths isn't a valid directory. 
  *)
  let rec get_files_from_explore_paths (explore_paths: string list): string list =
    let file_filter (filename: string): bool =
      Filename.check_suffix filename ".c" || Filename.check_suffix filename ".h" || Filename.check_suffix filename ".gh"
    in
    match explore_paths with
      | [] -> []
      | explore_path :: tail -> 
        let list_files = Array.to_list (Sys.readdir explore_path) in
        let filter_files = List.filter file_filter list_files in
        let absolute_files = List.map (Filename.concat explore_path) filter_files in
        List.append absolute_files (get_files_from_explore_paths tail)
  in

  (* Extract a list of decl list from a list of filepaths. *)
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

  (* Extract a list of lemmas from a list of decl list. *)
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
  
  (* Attempts to convert a textual pattern into an AST expression. Returns an empty string on failure. *)
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

  (* 
    First return value is the textual representation of op.
    Second return value indicates whether op is a binary operator.
    Third return value indicates whether op is a symmetric operator. A symmetric operator must be binary.
  *)
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
    | BitAnd -> "&", true, true
    | BitXor -> "^", true, true
    | BitOr -> "|", true, true
    | ShiftLeft -> "<<", true, false
    | ShiftRight-> ">>", true, false
  in

  (* Returns true when a binary operator is not symmetric but has a "reverse" operator (e.g. < and >, <= and >=). *)
  let are_operators_opposite (op: operator) (other_op: operator): bool =
    match op with
      | Le -> (match other_op with Ge -> true | _ -> false)
      | Ge -> (match other_op with Le -> true | _ -> false)
      | Lt -> (match other_op with Gt -> true | _ -> false)
      | Gt -> (match other_op with Lt -> true | _ -> false)
      | _ -> false
  in

  (* Returns a textual representation of expr. *)
  let rec string_of_expr (expr: expr): string =

    let rec string_of_expr_list (expr_list: expr list): string =
      match expr_list with
        | [] -> ""
        | head :: [] -> string_of_expr head
        | head :: tail -> (string_of_expr head) ^ ", " ^ (string_of_expr_list tail)
    in

    let rec string_of_pat (pat: pat): string =
      match pat with
        | LitPat(expr) -> string_of_expr expr
        | VarPat(_, varname) ->"?" ^ varname
        | DummyPat -> "_"
        | CtorPat(_, name, pat_list) -> name ^ "(" ^ string_of_pat_list pat_list ^ " )"
    and string_of_pat_list (pat_list: pat list): string =
      match pat_list with
        | [] -> ""
        | head :: [] -> string_of_pat head
        | head :: tail -> (string_of_pat head) ^ ", " ^ (string_of_pat_list tail)
    in


    let rec string_of_type_ (type_: type_): string =

      let rec string_of_integer_rank (rank: int): string =
        if (rank = 0) then
          "char"
        else if (rank = 1) then
          "short"
        else if (rank = 2) then
          "int"
        else
          "long"
      in

      match type_ with
        | Bool -> "bool"
        | Void -> "void"
        | Int(sign, rank) -> (match sign with Unsigned -> "unsigned " | _ -> "") ^ string_of_integer_rank rank
        | RealType -> "real"
        | Float -> "float"
        | Double -> "double"
        | LongDouble -> "long double"
        | StructType(name) -> "struct " ^ name
        | PtrType(type_in) -> string_of_type_ type_in ^ " *"
        | FuncType(name) -> name
        | InductiveType(name, type_list) -> name ^ "(" ^ string_of_type_list type_list ^ ")" 
        | PureFuncType(type_1, type_2) -> "(" ^ string_of_type_ type_1 ^ ", " ^ string_of_type_ type_2 ^ ")"
        | ObjType(name) -> name
        | ArrayType(type_in) -> string_of_type_ type_in ^ "[]"
        | StaticArrayType(type_in, nb_elems) -> string_of_type_ type_in ^ "[" ^ string_of_int nb_elems ^ "]"
        | TypeParam(name) -> name
        | PackageName(name) -> name
        | RefType(type_in) -> string_of_type_ type_in
        | AbstractType(name) -> name
        | _ -> "unknown_type"
     and string_of_type_list (type_list: type_ list): string =
      match type_list with
        | [] -> ""
        | head :: [] -> string_of_type_ head
        | head :: tail -> (string_of_type_ head) ^ ", " ^ (string_of_type_list tail)
    in

    let rec string_of_type_expr (type_expr: type_expr): string =
      match type_expr with
        | StructTypeExpr(_, name_opt, _) -> (match name_opt with Some name -> name | _ -> "")
        | EnumTypeExpr(_, name_opt, _) -> (match name_opt with Some name -> name | _ -> "")
        | PtrTypeExpr(_, type_expr_in) -> string_of_type_expr type_expr_in ^ " *"
        | ArrayTypeExpr(_, type_expr_in) -> string_of_type_expr type_expr_in ^ "[]"
        | StaticArrayTypeExpr(_, type_expr_in, nb_elems) -> string_of_type_expr type_expr_in ^ "[" ^ string_of_int nb_elems ^ "]"
        | ManifestTypeExpr(_, type_) -> string_of_type_ type_
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
      | True(_) -> "true"
      | False(_) -> "false"
      | Null(_) -> "null"
      | Var(_, varname) -> varname
      | TruncatingExpr(_, expr_in) -> "Truncating(" ^ string_of_expr expr_in ^ ")"
      | Operation(_, operator, operands) -> 
        let (op_str, isBinary, _) = operator_info operator in
        if (isBinary) then
          string_of_expr (List.nth operands 0) ^ " " ^ op_str ^ " " ^ string_of_expr (List.nth operands 1)
        else
          op_str ^ string_of_expr (List.nth operands 0)
      | IntLit(_, integer, _, _, _) -> Big_int.string_of_big_int integer
      | RealLit(_, real) -> Num.string_of_num real
      | StringLit(_, str) -> "\"" ^ str ^ "\""
      | Read(_, expr_in, str) -> string_of_expr expr_in ^ "." ^ str
      | ArrayLengthExpr(_, expr_in) -> "ArrayLength " ^ string_of_expr expr_in ^ ")"
      | ReadArray(_, array_expr, index_expr) -> string_of_expr array_expr ^ "[" ^ string_of_expr index_expr ^ "]" 
      | Deref(_, expr_in) -> "*" ^ string_of_expr expr_in
      | CallExpr(_, name, _, _, args, _) -> name ^ "(" ^ string_of_pat_list args ^ ")"
      | ExprCallExpr(_, callee_expr, args_expr) -> string_of_expr callee_expr ^ "(" ^ string_of_expr_list args_expr ^ ")"
      | IfExpr(_, cond_expr, then_expr, else_expr) -> "(" ^ string_of_expr cond_expr ^") ? (" ^ string_of_expr then_expr ^ ") : (" ^ string_of_expr else_expr ^ ")"
      | CastExpr(_, type_cast, expr_in) -> "(" ^ string_of_type_expr type_cast ^ ")" ^ string_of_expr expr_in 
      | SizeofExpr(_, type_sizeof) -> "sizeof(" ^ string_of_type_expr type_sizeof ^ ")"
      | AddressOf(_, expr_in) -> "&" ^ string_of_expr expr_in
      | AssignExpr(_, rec_expr, val_expr) -> "(" ^ string_of_expr rec_expr ^ " = " ^ string_of_expr val_expr ^ ")"
      | PointsTo(_, expr_in, pat) -> "PointsTo(" ^ string_of_expr expr_in ^ ", " ^ string_of_pat pat ^ ")"
      | ExprAsn(_, expr_in) -> string_of_expr expr_in
      | Sep(_, lhs, rhs) -> (string_of_expr lhs) ^ " &*& " ^ (string_of_expr rhs)
      | IfAsn(_, cond_expr, then_expr, else_expr) -> "(" ^ string_of_expr cond_expr ^") ? (" ^ string_of_expr then_expr ^ ") : (" ^ string_of_expr else_expr ^ ")"
      | EmpAsn(_) -> "emp" 
      | CoefAsn(_, perm, expr_in) -> "[" ^ string_of_pat perm ^ "]" ^ string_of_expr expr_in 
      | _ -> "unknown"
  in

  (*
    If exactMatchOnly is true, the function checks that expr and pattern are the same AST expressions.
    If exactMatchOnly is false, the function checks that the given pattern exists somewhere in expr.

    If enableMappings is true, then the function may return a non-empty mapping list list. In that case, if the first
    return value is true, one must check that at least one of the list in mapping list list doesn't contain conflicting
    variable assignments in order to establish that expr and pattern are "equal" (in the sense determined by exactMatchOnly).

    The first return value indicates whether the expr and pattern are "equal", in the sense determined by the boolean arguments.
    The second return value contains established mappings between variable names starting with "_" in pattern and sub-expressions of expr.
  *)
  let are_expr_equal (expr: expr) (pattern: expr) (exactMacthOnly: bool) (enableMappings: bool) : bool * mapping list list =

    let rec check_expr_for_pattern (expr: expr) (pattern: expr) (exactMacthOnly: bool) : bool * mapping list list = 

      let combine_or ((res1, mappings1): bool * mapping list list) ((res2, mappings2): bool * mapping list list) : bool * mapping list list =
        let m1 = if (res1) then mappings1 else [] in
        let m2 = if (res2) then mappings2 else [] in
        res1 || res2, List.append m1 m2
      in

      let combine_and ((res1, mappings1): bool * mapping list list) ((res2, mappings2): bool * mapping list list) : bool * mapping list list =
        let m1 = if (res1 && List.length mappings1 > 0) then List.hd mappings1 else [] in
        let m2 = if (res2 && List.length mappings2 > 0) then List.hd mappings2 else [] in
        res1 && res2, [List.append m1 m2]
      in

      let check_expr_list_for_pattern (expr_list: expr list) (pattern: expr) : bool * mapping list list =
        List.fold_left (fun acc expr -> combine_or acc (check_expr_for_pattern expr pattern false)) (false, []) expr_list
      in

      let check_expr_list_for_pattern_list (expr_list: expr list) (pattern_list: expr list) : bool * mapping list list =
        List.fold_left (fun acc (expr, pattern) -> combine_and acc (check_expr_for_pattern expr pattern true)) (true, []) (zip2 expr_list pattern_list)
      in

      let rec check_pat_for_pattern (pat: pat) (pattern: expr) : bool * mapping list list =
        match pat with 
          | LitPat(expr) -> check_expr_for_pattern expr pattern false
          | VarPat(_) -> false, []
          | DummyPat -> false, []
          | CtorPat(_, _, pat_list) -> check_pat_list_for_pattern pat_list pattern
      and check_pat_list_for_pattern (pat_list: pat list) (pattern: expr): bool * mapping list list = 
        List.fold_left (fun acc pat -> combine_or acc (check_pat_for_pattern pat pattern)) (false, []) pat_list
      in

      let rec check_pat_equal (pat: pat) (pattern_pat: pat): bool * mapping list list =
        match (pat, pattern_pat) with 
          | DummyPat, DummyPat -> true, []
          | _, DummyPat when enableMappings -> true, []
          | LitPat(expr), LitPat(pattern_expr) -> check_expr_for_pattern expr pattern_expr true
          | VarPat(_), VarPat(_) -> true, []
          | CtorPat(_, name, pat_list), CtorPat(_, pattern_name, pattern_pat_list) 
              when name = pattern_name && List.length pat_list = List.length pattern_pat_list -> check_pat_list_equal_list pat_list pattern_pat_list
          | LitPat(expr), CtorPat(_, pattern_name, pattern_pat_list) -> 
            begin
              match expr with
                | CallExpr(_, name, _, _, args, _) when name = pattern_name && List.length args = List.length pattern_pat_list -> check_pat_list_equal_list args pattern_pat_list
                | _ -> false, []
            end
          | _ -> false, []
      and check_pat_list_equal_list (pat_list: pat list) (pattern_pat_list: pat list): bool * mapping list list = 
        List.fold_left (fun acc (pat_in, pattern_pat_in) -> combine_and acc (check_pat_equal pat_in pattern_pat_in)) (true, []) (zip2 pat_list pattern_pat_list)
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

      let check_if_then_else (if_terms: expr list) : bool * mapping list list =
        let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_list_for_pattern if_terms pattern in
        match pattern with
          | IfAsn(_, pattern_cond_expr, pattern_then_expr, pattern_else_expr) ->
            let pattern_if_terms = [pattern_cond_expr; pattern_then_expr; pattern_else_expr] in combine_or pattern_inside (check_expr_list_for_pattern_list if_terms pattern_if_terms)
          | IfExpr(_, pattern_cond_expr, pattern_then_expr, pattern_else_expr) ->
            let pattern_if_terms = [pattern_cond_expr; pattern_then_expr; pattern_else_expr] in combine_or pattern_inside (check_expr_list_for_pattern_list if_terms pattern_if_terms)
          | _ -> false, []
      in

      match pattern with
        | Var(_, varname) when enableMappings && compare "_" (String.make 1 varname.[0]) == 0 -> true, [ [(varname, expr)] ]
        | _ ->
          begin
            match expr with
              | True(_) -> (match pattern with True(_) -> true, [] | _ -> false, [])
              | False(_) -> (match pattern with False(_) -> true, [] | _ -> false, [])
              | Null(_) -> (match pattern with Null(_) -> true, [] | _ -> false, [])
              | Var(_, varname) -> (match pattern with Var(_, pattern_varname) when varname = pattern_varname -> true, [] | _ -> false, [])
              | TruncatingExpr(_, expr_in) ->
                let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                begin
                  match pattern with
                    | TruncatingExpr(_, pattern_expr_in) -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                    | _ -> pattern_inside
                end
              | Operation(_, operator, operands) ->
                begin
                  let pattern_in_operands = if (exactMacthOnly) then false, [] else check_expr_list_for_pattern operands pattern in
                  match pattern with
                    | Operation(_, pattern_operator, pattern_operands) when List.length operands = List.length pattern_operands -> 
                      begin
                        let switch_operands_same = if (List.length operands < 2) then false, []
                          else combine_and (check_expr_for_pattern (List.nth operands 0) (List.nth pattern_operands 1) true) (check_expr_for_pattern (List.nth operands 1) (List.nth pattern_operands 0) true) 
                        in
                        let operands_same = check_expr_list_for_pattern_list operands pattern_operands in

                        let all_operands_match = 
                          if (operator = pattern_operator) then 
                            let (_, isBinary, isSymmetric) = operator_info operator in
                            if (isBinary && isSymmetric) then
                              combine_or switch_operands_same operands_same
                            else
                              operands_same
                          else if (are_operators_opposite operator pattern_operator) then
                            switch_operands_same
                          else
                            false, []
                        in
                        combine_or pattern_in_operands all_operands_match
                      end
                    | _ -> pattern_in_operands
                end
              | IntLit(_, integer, _, _, _) -> 
                begin
                  match pattern with 
                    | IntLit(_, pattern_integer, _, _, _) when (Big_int.compare_big_int integer pattern_integer) = 0 -> true, []
                    | _ -> false, []
                end
              | RealLit(_, real) ->
                begin
                  match pattern with
                    | RealLit(_, pattern_real) when Num.eq_num real pattern_real -> true, []
                    | _ -> false, []
                end
              | StringLit(_, str) ->
                begin
                  match pattern with
                    | StringLit(_, pattern_str) when str = pattern_str -> true, []
                    | _ -> false, []
                end
              | Read(_, expr_in, str) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with
                    | Read(_, pattern_expr_in, pattern_str) when str = pattern_str -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                    | _ -> pattern_inside
                end
              | ArrayLengthExpr(_, expr_in) -> 
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with
                    | ArrayLengthExpr(_, pattern_expr_in) -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                    | _ -> pattern_inside
                end
              | ReadArray(_, array_expr, index_expr) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else combine_or (check_expr_for_pattern array_expr pattern false) (check_expr_for_pattern index_expr pattern false) in
                  match pattern with
                      | ReadArray(_, pattern_array_expr, pattern_index_expr) -> 
                        let res_exact_match = combine_and (check_expr_for_pattern array_expr pattern_array_expr true) (check_expr_for_pattern index_expr pattern_index_expr true) in
                        combine_or pattern_inside res_exact_match
                      | _ -> pattern_inside
                end
              | Deref(_, expr_in) -> 
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with
                    | Deref(_, pattern_expr_in) -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true) 
                    | _ -> pattern_inside
                end
              | CallExpr(_, name, _, _, args, _) ->
                begin
                  let pattern_in_args = if (exactMacthOnly) then false, [] else check_pat_list_for_pattern args pattern in
                  match pattern with
                    | CallExpr(_, pattern_name, _, _, pattern_args, _) when name = pattern_name && List.length args = List.length pattern_args ->
                      begin
                        let each_arg_same = check_pat_list_equal_list args pattern_args in
                        combine_or each_arg_same pattern_in_args
                      end
                    | _ -> pattern_in_args
                
                end
              | ExprCallExpr(_, callee_expr, args_expr) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, []
                    else combine_or (check_expr_for_pattern callee_expr pattern false) (check_expr_list_for_pattern args_expr pattern)
                  in
                  match pattern with
                    | ExprCallExpr(_, pattern_callee_expr, pattern_args_expr) -> 
                      let res_exact_match = combine_and (check_expr_for_pattern callee_expr pattern_callee_expr true) (check_expr_list_for_pattern_list args_expr pattern_args_expr) in
                      combine_or pattern_inside res_exact_match
                    | _ -> pattern_inside
                end
              | IfExpr(_, cond_expr, then_expr, else_expr) -> check_if_then_else [cond_expr; then_expr; else_expr]
              | CastExpr(_, type_cast, expr_in) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with 
                    | CastExpr(_, pattern_type_cast, pattern_expr_in) -> 
                      if (check_type_expr_equal type_cast pattern_type_cast) then
                        combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                      else
                        pattern_inside
                    | _ -> pattern_inside
                end
              | SizeofExpr(_, type_sizeof) -> (match pattern with SizeofExpr(_, pattern_type_sizeof) -> (check_type_expr_equal type_sizeof pattern_type_sizeof), [] | _ -> false, [])
              | AddressOf(_, expr_in) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with
                    | AddressOf(_, pattern_expr_in) -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                    | _ -> pattern_inside 
                end
              | AssignExpr(_, rec_expr, val_expr) -> 
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else combine_or (check_expr_for_pattern rec_expr pattern false) (check_expr_for_pattern val_expr pattern false) in
                  match pattern with
                      | AssignExpr(_, pattern_rec_expr, pattern_val_expr) -> 
                      let res_exact_match = combine_and (check_expr_for_pattern rec_expr pattern_rec_expr true) (check_expr_for_pattern val_expr pattern_val_expr true) in
                        combine_or pattern_inside res_exact_match 
                      | _ -> pattern_inside
                end
              | PointsTo(_, expr_in, pat) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else combine_or (check_expr_for_pattern expr_in pattern false) (check_pat_for_pattern pat pattern) in
                  match pattern with
                    | PointsTo(_, pattern_expr_in, pattern_pat) -> 
                      let res_exact_match = combine_and (check_expr_for_pattern expr_in pattern_expr_in true) (check_pat_equal pat pattern_pat) in
                      combine_or pattern_inside res_exact_match 
                    | _ -> pattern_inside 
                end
              | ExprAsn(_, expr_in) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else check_expr_for_pattern expr_in pattern false in
                  match pattern with
                    | ExprAsn(_, pattern_expr_in) -> combine_or pattern_inside (check_expr_for_pattern expr_in pattern_expr_in true)
                    | _ -> pattern_inside 
                end
              | Sep(_, lhs, rhs) -> 
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else combine_or (check_expr_for_pattern lhs pattern false) (check_expr_for_pattern rhs pattern false) in
                  match pattern with
                    | Sep(_, pattern_lhs, pattern_rhs) ->
                      let res_exact_match = combine_and (check_expr_for_pattern lhs pattern_lhs true) (check_expr_for_pattern rhs pattern_rhs true) in
                      combine_or pattern_inside res_exact_match 
                    | _ -> pattern_inside
                end
              | IfAsn(_, cond_expr, then_expr, else_expr) -> check_if_then_else [cond_expr; then_expr; else_expr]
              | EmpAsn(_) -> (match pattern with EmpAsn(_) -> true, [] | _ -> false, [])
              | CoefAsn(_, perm, expr_in) ->
                begin
                  let pattern_inside = if (exactMacthOnly) then false, [] else combine_or (check_pat_for_pattern perm pattern) (check_expr_for_pattern expr_in pattern false) in
                  match pattern with
                    | CoefAsn(_, pattern_perm, pattern_expr_in) -> 
                      let res_exact_match = combine_and (check_pat_equal perm pattern_perm) (check_expr_for_pattern expr_in pattern_expr_in true) in
                      combine_or pattern_inside res_exact_match
                    | _ -> pattern_inside
                end
              | _ -> false, []
          end
    in

    check_expr_for_pattern expr pattern exactMacthOnly
  in

  (* 
    Checks that at least one list of mappings in mappings_list is valid, in the sense that it doesn't contain conflicting variable mappings. 
    Meant to be used on the second return value of are_expr_equal, when the first return value is true.
  *)
  let rec check_mappings_valid (mappings_list: mapping list list): bool =

    let rec check_mappings_valid_inner (mappings: mapping list): bool =
      match mappings with
        | [] -> true
        | (varname, expr) :: _ ->

          let rec solve_conflicts (expr_list: expr list): bool =
            match expr_list with
              | [] -> true
              | expr :: tail -> 
                let same_expr_filter other_expr = let (res, _) = are_expr_equal expr other_expr true false in res in
                let same_expr_list = List.filter same_expr_filter tail in
                List.length tail = List.length same_expr_list
          in

          let conflicts = List.filter (fun (other_varname, _) -> varname = other_varname) mappings in
          let expr_list = List.map (fun (_, expr) -> expr) conflicts in
          solve_conflicts expr_list && check_mappings_valid_inner (List.filter (fun (other_varname, _) -> varname <> other_varname) mappings)
    in

    match mappings_list with
      | [] -> false
      | mappings :: tail -> check_mappings_valid_inner mappings || check_mappings_valid tail
  in

  (* Searches for a pattern in a list of lemma post-conditions. Displays matches on stdout. *)
  let search_for_pattern (lemmas: lemma list) (pattern: expr): unit =

    let filename_from_loc (loc: loc): string =
      match loc with
        | Lexed(loc0) -> let ((p1, _, _), _) = loc0 in p1
        | _ -> ""
    in

    let lines_from_loc (loc: loc): string =
      match loc with
        | Lexed(loc0) -> 
          let ((_, l1, _), _) = loc0 in 
          let l1_str = string_of_int l1 in
          let str = ref l1_str in
          let _ = for i = 0 to 3 - String.length l1_str do str := " " ^ !str done in
          !str
        | _ -> ""
    in  

    let rec search_for_pattern_inner (lemmas_inner: lemma list) (last_filename: string) : unit =
      match lemmas_inner with
        | [] -> ()
        | (loc, name, postcond) :: tail ->
          begin
            let (res, mappings) = are_expr_equal postcond pattern false true in
            if (res && check_mappings_valid mappings) then 
              let filename = filename_from_loc loc in
              let _ = 
                if (filename <> last_filename) then 
                  Printf.printf "\nIn file %s:\n" filename 
                else 
                  ()
              in
              let _ = Printf.printf "\tAt line %s: %s -- ensures %s\n" (lines_from_loc loc) name (string_of_expr postcond) in
              search_for_pattern_inner tail filename
            else 
              search_for_pattern_inner tail last_filename
          end
    in
    search_for_pattern_inner lemmas ""
  in

  (* 
    Submits a pattern for matching against all parsed lemmas. 
    If pattern_str can't be parsed to a valid AST expression, prints an error message and returns. 
    Displays matches on stdout. 
  *)
  let submit_pattern (lemmas: lemma list) (pattern_str: string): unit =
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
      | Some(pattern_expr) -> search_for_pattern lemmas pattern_expr
      | None -> ()
  in

  (* 
    Returns true iff lemma comes from a .c file and has a matching declaration in a .gh file. 
    Meant to be used as List.filter (remove_duplicate_lemmas lemma_list) lemma_list.
  *)
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
            let (res, _) = are_expr_equal postcond postcond_in true false in
            if (Filename.check_suffix (filename_from_loc loc_in) ".gh" && name = name_in && res) then
              false
            else 
              check_for_duplicate tail
      in
      check_for_duplicate lemmas
    else
      true
  in

  (* Converts a relative path to an absolute path. If the given path is already absolute, it is returned as is. *)
  let rel_to_abs_path (path: string): string =
    if (Filename.is_relative path) then
      let length = String.length path in
      let length_current_dir = String.length Filename.current_dir_name in
      let length_parent_dir = String.length Filename.parent_dir_name in
      if (length_parent_dir <= length && String.sub path 0 length_parent_dir = Filename.parent_dir_name) then
        Sys.getcwd () ^ Filename.dir_sep ^ path
      else if (length_current_dir <= length && String.sub path 0 length_current_dir = Filename.current_dir_name) then
        Sys.getcwd () ^ (String.sub path 1 (length - length_current_dir))
      else 
        path
    else
      path
  in

  (* Command line variables go here *)
  let include_paths: string list ref = ref [] in
  let define_macros: string list ref = ref [] in
  let explore_paths: string list ref = ref [] in
  let cla_patterns: string list ref = ref [] in

  (* CLA syntax definition *)
  let cla = [ "-I", String (fun str -> include_paths := rel_to_abs_path str :: !include_paths), "<path> Add a directory to the list of directories to be searched for header files." 
            ; "-D", String (fun str -> define_macros := str :: !define_macros), "<string> Predefine name as a macro, with definition 1."
            ; "-P", String (fun str -> cla_patterns := List.append !cla_patterns [str]), "<VeriFast expression> Add a pattern to search for and disables interactive mode."
            ]
  in

  (* Parse command-line arguments *)
  parse cla (fun str -> explore_paths := rel_to_abs_path str :: !explore_paths) usage_msg;

  (* Displays help and stop if no directories to explore were provided *)
  let _ = 
    if (List.length !explore_paths = 0) then
      let _ = Printf.printf "%s" (usage_string cla usage_msg) in
      exit 0
    else
      ()
  in

  (* Extract lemmas from lemma-defining directories *)
  let files_to_explore = 
    try
      get_files_from_explore_paths !explore_paths
    with
      Sys_error(msg) -> let _ = Printf.printf "%s\nAborting\n" msg in exit 1
  in
  let decls_to_explore = get_decls_from_filepaths files_to_explore !include_paths !define_macros in
  let lemmas_to_explore = get_lemmas_from_decls decls_to_explore in
  let lemmas_filtered = List.filter (remove_duplicate_lemmas lemmas_to_explore) lemmas_to_explore in
  let _ = Printf.printf "\n== %d lemmas were parsed and will be searched for a pattern ==\n\n" (List.length lemmas_filtered) in

  if (List.length !cla_patterns <> 0) then (* Non-interactive mode *)
    (* Submit all provided patterns for matching *)
    let rec submit_patterns (patterns: string list): unit =
      match patterns with
        | [] -> ()
        | pattern_str :: tail -> (Printf.printf "\n-> %s\n" pattern_str; submit_pattern lemmas_filtered pattern_str; submit_patterns tail)
    in
    submit_patterns !cla_patterns
  else (* Interactive mode *)
    (* Execution loop *)
    while true do
      Printf.printf "\nEnter a pattern > ";
      let pattern_str = read_line () in
      submit_pattern lemmas_filtered pattern_str
    done
