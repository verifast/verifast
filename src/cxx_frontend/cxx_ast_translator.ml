module Stubs = Stubs_ast.Make(Capnp.BytesMessage)
module R = Stubs.Reader
module VF = Ast
open Util
open Big_int

(**
  [capnp_arr_map f arr] applies [f] to every element of cap'n proto array [arr] and return a new list containing those elements.
*)
let capnp_arr_map (f: 'a -> 'b) (arr: (Stubs_ast.ro, 'a, R.array_t) Capnp.Array.t): 'b list =
  arr |> Capnp.Array.map_list ~f

(**
  [capnp_arr_iter] applies [f] to every element of cap'n proto array [arr].
*)
let capnp_arr_iter (f: 'a -> 'b) (arr: (Stubs_ast.ro, 'a, R.array_t) Capnp.Array.t): unit =
  arr |> Capnp.Array.iter ~f

let union_no_init_err kind =
  failwith @@ "Node of kind '" ^ kind ^ "' has no initialized union body (default case has been implicitly selected). Make sure that you serialize a description for all nodes in the C++ AST exporter tool."

exception CxxAstTranslException of VF.loc * string

let error (loc: VF.loc) (msg: string): 'a =
  raise @@ CxxAstTranslException (loc, msg)

module Make (Args: Cxx_fe_sig.CXX_TRANSLATOR_ARGS) : Cxx_fe_sig.Cxx_Ast_Translator = struct

  (* 
    Maps unique identifiers - integers - to filenames.
    Every source location from Clang is passed as {i (int, int, int)} where
    the first integer represents the file. This map is used to retrieve the filename.
   *)
  let files_table: (int, string) Hashtbl.t = Hashtbl.create 8

  let get_fd_path = Hashtbl.find files_table

  (*
    Maps unique identifiers - integers - to the declarations that are part of the file with that identifier.
    Allows to process declarations of a file in isolation from other files.
  *)
  let decls_table: (int, VF.decl list) Hashtbl.t = Hashtbl.create 4

  let pop_fd_decls_opt fd = 
    let result = Hashtbl.find_opt decls_table fd in
    Hashtbl.remove decls_table fd;
    result

  let pop_fd_decls fd =
    let Some res = pop_fd_decls_opt fd in
    res

  (*
    Parser which is used to translate VeriFast annotations.
  *)
  module AP = Cxx_annotation_parser.Make(Args)

  let int_rank, long_rank, ptr_rank = Parser.decompose_data_model Args.data_model_opt

  let make_int_lit (loc: VF.loc) (n: int) =
    VF.IntLit (loc, big_int_of_int n, true, false, VF.NoLSuffix)

  (**
    [invoke_exporter path allow_expansions] runs the C++ AST exporter. This tool visits each node
    in the C++ AST and serializes it. It also checks if every macro expansion is context free. 
    [allow_expansions] is a list of macros that should be allowed to expand, even
    if they depend on the context where they are included. 
    
    Returns ({i in_channel}, {i out_channel}, {i error_channel}), which should be closed afterwards.
    The serialized AST will be transmitted through {i in_channel} in case of success. Otherwise an error
    is transmitted through {i error_channel}. {i out_channel} should not be used.

    In case of success, the exporter first transmits a message {i SerResult.Ok} through {i in_channel} 
    to report that the compilation, context free macro expansion check, and AST serialization were successful.
    The next message that is trasmitted through {i in_channel} represents the serialized C++ AST.

    Otherwise a message {i SerResult.Error} is transmitted through {i error_channel}
    if any error occurred during compilation, context free macro expansion checking, or AST serialization.
    This error message contains an explanation why the C++ AST exporter produced an error.
  *)
  let invoke_exporter (file: string) (allow_expansions: string list) =
    let bin_dir = Filename.dirname Sys.executable_name in
    let cmd = Printf.sprintf "%s/vf-cxx-ast-exporter %s -allow_macro_expansion=%s -- -I %s" bin_dir file (String.concat "," allow_expansions) bin_dir in
    let inchan, outchan, errchan = Unix.open_process_full cmd [||] in
    inchan, outchan, errchan

  (**
    [subs_ast_inc_channel pipe] creates a read context to dezerialize cap'n proto messages from the given
    [pipe]. This read context can be used to read multiple cap'n proto messages.
  *)
  let stubs_ast_in_channel pipe =
    Capnp_unix.IO.create_read_context_for_channel ~compression:`None pipe

  (**
    [read_capn_message read_context] reads {e one} cap'n proto message from [read_context].
  *)
  let read_capnp_message read_context =
    Capnp_unix.IO.ReadContext.read_message read_context

  let transl_loc (loc: R.Loc.t) =
    let open R.Loc in
    let transl_srcpos srcpos =
      let l = SrcPos.l_get srcpos in
      let c = SrcPos.c_get srcpos in
      let fd = SrcPos.fd_get srcpos in
      let file_name = get_fd_path fd in
      file_name, l, c 
    in
    let l_start = if has_start loc then start_get loc |> transl_srcpos else VF.dummy_srcpos in
    let l_end = if has_end loc then end_get loc |> transl_srcpos else VF.dummy_srcpos in
    VF.Lexed (l_start, l_end)

  let map_ann_clause ann =
    let open R.Clause in
    let VF.Lexed a_loc = loc_get ann |> transl_loc in
    let a_text = text_get ann in
    a_loc, a_text

  (*************)
  (* top level *)
  (*************)

  (**
    [decompose_node node] decomposes [node] to a tuple consisting of a VeriFast location of [node]
    and a cap'n proto pointer pointing to [node].
  *)
  let decompose_node (node: R.Node.t): VF.loc * 'a Stubs.reader_t =
    let open R.Node in
    let loc = loc_get node in
    let desc = desc_get node in
    transl_loc loc, R.of_pointer desc

  (**
    [transl_expext f node] applies [f] to [node] and fails if the result of that application was {i None}.
  *)
  let transl_expect (f: VF.loc -> 'b -> 'c option) (node: R.Node.t): 'c =
    let loc, ptr = decompose_node node in
    match f loc ptr with
    | None -> failwith "Actual did not match expected."
    | Some result -> result

  let transl_node (f: VF.loc -> 'a Stubs.reader_t -> 'b) (node: R.Node.t): 'b =
    let loc, ptr = decompose_node node in
    f loc ptr

  (**
    [transl_decl decl] translates [decl] and returns a VeriFast declaration list, representing [decl].
  *)
  let rec transl_decl (decl_node: R.Node.t): VF.decl list =
    let open R.Decl in
    let loc, desc = decompose_node decl_node in
    match get desc with
    | UnionNotInitialized -> union_no_init_err "declaration"
    | Empty               -> []
    | Function f          -> [transl_func_decl loc f]
    | Ann a               -> transl_ann_decls loc a
    | Record r            -> transl_record_decl loc r
    | Method m            -> [transl_meth_decl loc m]
    | Var v               -> [transl_var_decl_global loc v]
    | EnumDecl d          -> [transl_enum_decl loc d]
    | Typedef d           -> [transl_typedef_decl loc d]
    | Ctor c              -> if (R.Decl.Ctor.implicit_get c) then [] else [transl_ctor_decl loc c]
                              (* TODO: we currently skip implicit constructors because they can contain lValueRefs/rValueRefs *)
    | AccessSpec          
    | DefDestructor       -> [] (* we currently don't care about these *)
    | Undefined _         -> failwith "Undefined declaration."
    | _                   -> error loc "Unsupported declaration."

  (**
    [transl_expr expr] translates [expr] and returns a VeriFast expression, representing [expr].
  *)
  and transl_expr (expr_node: R.Node.t): VF.expr =
    let open R.Expr in
    let loc, desc = decompose_node expr_node in
    match get desc with
    | UnionNotInitialized -> union_no_init_err "expression"
    | UnaryOp op          -> transl_unary_op_expr loc op
    | BinaryOp op         -> transl_binary_op_expr loc op
    | IntLit int_lit      -> transl_int_lit_expr loc int_lit
    | BoolLit bool_lit    -> transl_bool_lit_expr loc bool_lit
    | StringLit str_lit   -> transl_str_lit_expr loc str_lit
    | Call c              -> transl_call_expr loc c
    | DeclRef ref         -> transl_decl_ref_expr loc ref
    | This                -> transl_this_expr loc
    | New n               -> transl_new_expr loc n
    | Construct c         -> transl_construct_expr loc c
    | Member m            -> transl_member_expr loc m
    | MemberCall c        -> transl_call_expr loc c
    | NullPtrLit          -> transl_null_ptr_lit_expr loc
    | Delete d            -> transl_delete_expr loc d
    | Undefined _         -> failwith "Undefined expression"
    | _                   -> error loc "Unsupported expression."

  (**
    [transl_stmt stmt] translates [stmt] and returns a VeriFast statement, representing [stmt].
  *)
  and transl_stmt (stmt_node: R.Node.t): VF.stmt =
    let open R.Stmt in
    let loc, desc = decompose_node stmt_node in
    match get desc with
    | UnionNotInitialized -> union_no_init_err "statement"
    | Decl decls          -> transl_decl_stmt loc decls
    | Ann a               -> transl_stmt_ann loc a
    | Expr e              -> transl_expr_stmt e
    | Return r            -> transl_return_stmt loc r
    | If i                -> transl_if_stmt loc i
    | Null                -> transl_null_stmt loc
    | While w             -> transl_while_stmt loc w
    | DoWhile w           -> transl_do_while_stmt loc w
    | Break               -> transl_break_stmt loc
    | Compound c          -> transl_compound_stmt loc c
    (* TODO: check if this is translated correctly *)
    (* | Switch s            -> transl_switch_stmt loc s *)
    | Undefined _         -> failwith "Undefined statement."
    | _                   -> error loc "Unsupported statement."

  (**
    [transl_stmt_as_list stmt] translates [stmt] to a VeriFast statment list and the VeriFast location of the right brace.
    It will return a list of one statement and its location in case [stmt] does not represent a compound statement.
  *)
  and transl_stmt_as_list (stmt_node: R.Node.t): VF.stmt list * VF.loc =
    let open R.Stmt in
    let loc, desc = decompose_node stmt_node in
    match get desc with
    | Compound c -> R.Stmt.Compound.stmts_get c |> capnp_arr_map transl_stmt, transl_loc @@ R.Stmt.Compound.r_brace_get c
    | _ -> [transl_stmt stmt_node], loc

  (**
    [transl_type ?loc ty] translates [ty] and returns a VeriFast type expression, representing [ty].
    [loc] should be passed if the location of the type expression in its source code is known.
  *)
  and transl_type ?(loc: VF.loc = VF.dummy_loc) (ty: R.Type.t): VF.type_expr =
    match R.Type.get ty with
    | Builtin b     -> transl_builtin_type loc b
    | Pointer p     -> transl_pointer_type loc p
    | PointerLoc p  -> transl_pointer_loc_type loc p
    | Record r      -> transl_record_type loc r
    | EnumType t    -> transl_enum_type loc t
    | Undefined _   -> failwith "Undefined type."
    | _             -> error loc "Unsupported type."

  (**
    [transl_type_loc ty] translates [ty] and returns a VeriFast type expression, representing [ty].
    The difference with [transl_type] is that [ty] represents a node which also contains the location of the type.
  *)
  and transl_type_loc (type_node: R.Node.t): VF.type_expr =
    let open R.Type in
    let loc, desc = decompose_node type_node in
    transl_type desc ~loc

  (****************)
  (* declarations *)
  (****************)

  and transl_func (f: R.Decl.Function.t) = 
    let open R.Decl.Function in
    let name = name_get f in
    let mangled_name = mangled_name_get f in 
    let body_opt = 
      if has_body f then Some (transl_stmt_as_list @@ body_get f)
      else None 
    in
    let contract = contract_get f in
    let contract_lst = contract |> capnp_arr_map map_ann_clause in
    let ng_callers_only, ft, pre_post, terminates = AP.parse_spec_clauses contract_lst in
    let return_type = 
      match transl_type_loc @@ result_get f with
      | VF.ManifestTypeExpr (_, VF.Void) -> None
      | rt -> Some rt 
    in
    let transl_param param = 
      let open R.Decl.Param in
      if has_default param then failwith "Parameters with default expressions are not supported yet."
      else transl_type_loc @@ type_get param, name_get param 
    in
    let params = params_get f |> capnp_arr_map transl_param in
    name, mangled_name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type

  and transl_func_decl (loc: VF.loc) (f: R.Decl.Function.t): VF.decl =
    let _, name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type = transl_func f in
    let make_return loc = VF.ReturnStmt (loc, Some (make_int_lit loc 0)) in
    let body_stmts = 
      match name, body_opt with
      | "main", Some ([], l) -> Some ([make_return l], l)
      | "main", Some (body, l) -> begin match List.rev body with
        | VF.ReturnStmt _ :: _ -> body_opt
        | _ -> Some (body @ [make_return l], l)
        end 
      | _ -> body_opt 
    in
    VF.Func (loc, VF.Regular, [], return_type, name, params, ng_callers_only, ft, pre_post, terminates, body_stmts, VF.Static, VF.Public)

  and transl_ann_decls (loc: VF.loc) (text: string): VF.decl list =
    let VF.Lexed l = loc in
    AP.parse_decls (l, text)

  and transl_var_init (i: R.Decl.Var.VarInit.t): VF.expr =
    let open R.Decl.Var.VarInit in
    let init_expr = init_get i |> transl_expr in 
    match style_get i with
    | R.Decl.Var.InitStyle.CInit -> init_expr
    | _ -> error (VF.expr_loc init_expr) "Only c-style initialization is supported at the moment."

  and transl_var (var: R.Decl.Var.t): VF.type_expr * string * VF.expr option =
    let open R.Decl.Var in
    let name = name_get var in
    let init_opt = 
      if has_init var then Some (init_get var |> transl_var_init)
      else None 
    in
    let ty = transl_type_loc @@ type_get var in
    ty, name, init_opt

  (* used in declaration statements *)
  and transl_var_decl_local (loc: VF.loc) (var: R.Decl.Var.t): VF.loc * VF.type_expr * string * VF.expr option * (bool ref * string list ref option ref) =
    let ty, name, init_opt = transl_var var in
    loc, ty, name, init_opt, (ref false, ref None)

  (* used at global level, i.e., outside functions, methods... *)
  and transl_var_decl_global (loc: VF.loc) (var: R.Decl.Var.t): VF.decl =
    let ty, name, init_opt = transl_var var in
    VF.Global (loc, ty, name, init_opt)

  (* every declaration in the record that is not a field is translated as a separate declaration *)
  and transl_record_decl (loc: VF.loc) (record: R.Decl.Record.t): VF.decl list =
    let open R.Decl.Record in
    let name = name_get record in
    let body, decls = 
      if has_body record then
        let open Body in
        let body = body_get record in
        let fields = fields_get body |> capnp_arr_map (transl_node transl_field_decl) in
        let decls = decls_get body |> capnp_arr_map transl_decl |> List.flatten in
        Some fields, decls
      else None, [] 
    in
    let vf_record = 
      match kind_get record with
      | R.RecordKind.Struc | R.RecordKind.Class -> VF.Struct (loc, name, body, []) 
      | R.RecordKind.Unio -> VF.Union (loc, name, body) 
    in
    vf_record :: decls

  and transl_meth (meth: R.Decl.Method.t) =
    let open R.Decl.Method in
    let name, mangled_name, params, body_opt, anns, return_type = func_get meth |> transl_func in
    let binding = if static_get meth then VF.Static else VF.Instance in
    let params = 
      match binding with
      | VF.Static -> params
      | VF.Instance -> 
        let this_type = transl_type @@ this_get meth in
        (VF.PtrTypeExpr (VF.dummy_loc, this_type), "this") :: params 
    in
    name, mangled_name, params, body_opt, anns, return_type

  (* translates a method to a function and prepends 'this' to the parameters in case it is not a static method *)
  and transl_meth_decl (loc: VF.loc) (meth: R.Decl.Method.t): VF.decl =
    let open R.Decl.Method in
    let _, mangled_name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type = transl_meth meth in
    VF.Func (loc, VF.Regular, [], return_type, mangled_name, params, ng_callers_only, ft, pre_post, terminates, body_opt, VF.Static, VF.Public)

  and transl_record_ref (loc: VF.loc) (record_ref: R.RecordRef.t): VF.type_ =
    let open R.RecordRef in
    let name = name_get record_ref in
    match kind_get record_ref with
    | R.RecordKind.Struc
    | R.RecordKind.Class -> VF.StructType name
    | R.RecordKind.Unio -> VF.UnionType name
    | _ -> error loc "Invalid record reference"

  and transl_ctor_decl (loc: VF.loc) (ctor: R.Decl.Ctor.t): VF.decl =
    let open R.Decl.Ctor in
    let _, mangled_name, this_param :: params, body_opt, (_, _, pre_post_opt, terminates), _ = method_get ctor |> transl_meth in
    (* the init list also contains member names that are default initialized and don't appear in the init list *)
    (* in that case, no init expr is present (we can always retrieve it from the field default initializer) *)
    let transl_init init =
      let open CtorInit in
      name_get init, if has_init init then Some (init_get init |> transl_expr, is_written_get init) else None in
    let body_opt = body_opt |> option_map @@ fun body ->
      let init_list = init_list_get ctor |> capnp_arr_map transl_init in
      init_list, body in
    let implicit = implicit_get ctor in
    let parent = ctor |> parent_get |> transl_record_ref loc in
    VF.CxxCtor (loc, mangled_name, params, pre_post_opt, terminates, body_opt, implicit, parent)

  and transl_field_decl (loc: VF.loc) (field: R.Decl.Field.t): VF.field =
    let open R.Decl.Field in
    let name = name_get field in
    let ty = type_get field |> transl_type_loc in
    let init_opt =
      if has_init field then
        let init = init_get field in
        let open FieldInit in
        let init_expr = init_get init |> transl_expr in
        match style_get init with
        | InitStyle.CopyInit -> Some init_expr
        | _ -> error loc "Only copy initialization is supported at the moment."
      else None 
    in
    VF.Field (loc, VF.Real, ty, name, VF.Instance, VF.Public, false, init_opt)

  and transl_enum_decl (loc: VF.loc) (decl: R.Decl.Enum.t): VF.decl =
    let open R.Decl.Enum in
    let name = name_get decl in
    let transl_enum_field field = 
      let name = EnumField.name_get field in
      let expr_opt = 
        if EnumField.has_expr field then Some (transl_expr @@ EnumField.expr_get field)
        else None 
      in
      name, expr_opt 
    in
    let fields = fields_get decl |> capnp_arr_map transl_enum_field in
    VF.EnumDecl (loc, name, fields)

  and transl_typedef_decl (loc: VF.loc) (decl: R.Decl.Typedef.t): VF.decl =
    let open R.Decl.Typedef in
    let name = name_get decl in
    let ty = type_get decl |> transl_type_loc in
    VF.TypedefDecl (loc, ty, name)

  (***************)
  (* expressions *)
  (***************)

  and transl_unary_op_expr (loc: VF.loc) (op: R.Expr.UnaryOp.t): VF.expr =
    let open R.Expr.UnaryOp in
    let operand = transl_expr @@ operand_get op in
    let make_assign loc op lhs post =
      VF.AssignOpExpr (loc, lhs, op, make_int_lit loc 1, post) 
    in
    match kind_get op with
    | R.UnaryOpKind.Plus    -> operand (* +i *)
    | R.UnaryOpKind.Minus   -> VF.Operation (loc, VF.Sub, [make_int_lit loc 0; operand]) (* -i *)
    | R.UnaryOpKind.Not     -> VF.Operation (loc, VF.BitNot, [operand]) (* ~ *)
    | R.UnaryOpKind.LNot    -> VF.Operation (loc, VF.Not, [operand]) (* ! *)
    | R.UnaryOpKind.AddrOf  -> VF.AddressOf (loc, operand) (* &i *)
    | R.UnaryOpKind.Deref   -> VF.Deref (loc, operand) (* *i *)
    | R.UnaryOpKind.PreInc  -> make_assign loc VF.Add operand false (* --i *)
    | R.UnaryOpKind.PreDec  -> make_assign loc VF.Sub operand false (* ++i *)
    | R.UnaryOpKind.PostInc -> make_assign loc VF.Add operand true (* i++ *)
    | R.UnaryOpKind.PostDec -> make_assign loc VF.Sub operand true (* i-- *)
    | _                     -> error loc "Unsupported unary expression."

  and transl_binary_op_expr (loc: VF.loc) (op: R.Expr.BinaryOp.t): VF.expr =
    let open R.Expr.BinaryOp in
    let lhs = transl_expr @@ lhs_get op in
    let rhs = transl_expr @@ rhs_get op in
    let make_op loc op lhs rhs =
      VF.Operation (loc, op, [lhs; rhs]) 
    in
    let make_assign loc op lhs rhs =
      VF.AssignOpExpr (loc, lhs, op, rhs, false) 
    in
    match kind_get op with
    (* binary operators *)
    | R.BinaryOpKind.Add        -> make_op loc VF.Add lhs rhs (* + *)
    | R.BinaryOpKind.Sub        -> make_op loc VF.Sub lhs rhs (* - *)
    | R.BinaryOpKind.Mul        -> make_op loc VF.Mul lhs rhs (* * *)
    | R.BinaryOpKind.Div        -> make_op loc VF.Div lhs rhs (* / *)
    | R.BinaryOpKind.Rem        -> make_op loc VF.Mod lhs rhs (* % *)
    | R.BinaryOpKind.Shl        -> make_op loc VF.ShiftLeft lhs rhs (* << *)
    | R.BinaryOpKind.Shr        -> make_op loc VF.ShiftRight lhs rhs (* >> *)
    | R.BinaryOpKind.Lt         -> make_op loc VF.Lt lhs rhs (* < *)
    | R.BinaryOpKind.Gt         -> make_op loc VF.Gt lhs rhs (* > *)
    | R.BinaryOpKind.Le         -> make_op loc VF.Le lhs rhs (* <= *)
    | R.BinaryOpKind.Ge         -> make_op loc VF.Ge lhs rhs (* >= *)
    | R.BinaryOpKind.Eq         -> make_op loc VF.Eq lhs rhs (* == *)
    | R.BinaryOpKind.Ne         -> make_op loc VF.Neq lhs rhs (* != *)
    | R.BinaryOpKind.Or         -> make_op loc VF.BitOr lhs rhs (* | *)
    | R.BinaryOpKind.And        -> make_op loc VF.BitAnd lhs rhs (* & *)
    | R.BinaryOpKind.Xor        -> make_op loc VF.BitXor lhs rhs (* ^ *)
    | R.BinaryOpKind.LAnd       -> make_op loc VF.And lhs rhs (* && *)
    | R.BinaryOpKind.LOr        -> make_op loc VF.Or lhs rhs (* || *)
    (* regular assign *)
    | R.BinaryOpKind.Assign     -> VF.AssignExpr (loc, lhs, rhs) (* = *)
    (* assign operator *)
    | R.BinaryOpKind.MulAssign  -> make_assign loc VF.Mul lhs rhs (* *= *)
    | R.BinaryOpKind.DivAssign  -> make_assign loc VF.Div lhs rhs (* /= *)
    | R.BinaryOpKind.RemAssign  -> make_assign loc VF.Mod lhs rhs (* %= *)
    | R.BinaryOpKind.AddAssign  -> make_assign loc VF.Add lhs rhs (* += *)
    | R.BinaryOpKind.SubAssign  -> make_assign loc VF.Sub lhs rhs (* -= *)
    | R.BinaryOpKind.ShlAssign  -> make_assign loc VF.ShiftLeft lhs rhs (* <<= *)
    | R.BinaryOpKind.ShrAssign  -> make_assign loc VF.ShiftRight lhs rhs (* >>= *)
    | R.BinaryOpKind.AndAssign  -> make_assign loc VF.BitAnd lhs rhs (* &= *)
    | R.BinaryOpKind.XorAssign  -> make_assign loc VF.BitXor lhs rhs (* ^= *)
    | R.BinaryOpKind.OrAssign   -> make_assign loc VF.BitOr lhs rhs (* |= *)
    | _                         -> error loc "Unsupported binary expression."

  and transl_int_lit_expr (loc: VF.loc) (int_lit: R.Expr.IntLit.t): VF.expr =
    let open R.Expr.IntLit in
    let l_suf = 
      match l_suffix_get int_lit with
      | R.SufKind.LSuf -> VF.LSuffix
      | R.SufKind.LLSuf -> VF.LLSuffix
      | R.SufKind.NoSuf -> VF.NoLSuffix 
    in
    let str_value = value_get int_lit in
    let dec, value = 
      match base_get int_lit with
      | R.NbBase.Decimal -> true, big_int_of_string str_value
      | R.NbBase.Octal -> false, Lexer.big_int_of_octal_string str_value
      | R.NbBase.Hex -> false, Lexer.big_int_of_hex_string str_value 
    in
    let u_suf = u_suffix_get int_lit in
    VF.IntLit (loc, value, dec, u_suf, l_suf)

  and transl_bool_lit_expr (loc: VF.loc) (bool_lit: bool): VF.expr =
    match bool_lit with
    | true -> VF.True loc
    | false -> VF.False loc

  and transl_str_lit_expr (loc: VF.loc) (str_lit: string): VF.expr =
    VF.StringLit (loc, str_lit)

  and map_args (args: (Stubs_ast.ro, R.Node.t, R.array_t) Capnp.Array.t): VF.pat list =
    args |> capnp_arr_map (fun e -> VF.LitPat (transl_expr e))

  and transl_call_expr (loc: VF.loc) (call: R.Expr.Call.t): VF.expr =
    let open R.Expr.Call in
    let callee = callee_get call in
    let args = args_get call |> map_args in
    let name, args =
      let callee_loc, desc = decompose_node callee in
      let e = R.Expr.get desc in
      match e with
      | R.Expr.DeclRef r -> (* c-like function call, operator calls (even tho they can be class methods) *)
        let args = 
          if R.Expr.DeclRef.is_class_member_get r then 
            let VF.LitPat this_arg :: args = args in
            VF.LitPat (VF.AddressOf (callee_loc, this_arg)) :: args
          else args in
        R.Expr.DeclRef.mangled_name_get r, args
      | R.Expr.Member m ->  (* C++ method call on explicit or implicit (this) object *)
        let base = 
          let base_expr = transl_expr @@ R.Expr.Member.base_get m in
          (* methods/operators/conversions expect a pointer to the object as first argument *)
          if R.Expr.Member.base_is_pointer_get m then base_expr
          else VF.AddressOf (callee_loc, base_expr) in
        R.Expr.Member.mangled_name_get m, VF.LitPat base :: args 
      | _ -> error loc "Unsupported callee in function or method call." 
    in
    VF.CallExpr (loc, name, [], [], args, VF.Static)

  and transl_decl_ref_expr (loc: VF.loc) (ref: R.Expr.DeclRef.t): VF.expr =
    VF.Var (loc, R.Expr.DeclRef.name_get ref)

  and transl_this_expr (loc: VF.loc): VF.expr =
    VF.Var (loc, "this")

  and transl_construct_expr (loc: VF.loc) (c: R.Expr.Construct.t): VF.expr =
    let open R.Expr.Construct in 
    let mangled_name = mangled_name_get c in
    let ty = type_get c |> transl_type in
    let args = args_get c |> capnp_arr_map transl_expr in
    VF.CxxConstruct (loc, mangled_name, ty, args)

  and transl_new_expr (loc: VF.loc) (n: R.Expr.New.t): VF.expr =
    let open R.Expr.New in
    let expr_opt = 
      if has_expr n then Some (expr_get n |> transl_expr)
      else None
    in
    let ty = type_get n |> transl_type in
    VF.CxxNew (loc, ty, expr_opt)

  and transl_delete_expr (loc: VF.loc) (d: R.Node.t): VF.expr = 
    let e = transl_expr d in
    VF.CxxDelete (loc, e)

  and transl_member_expr (loc: VF.loc) (m: R.Expr.Member.t): VF.expr =
    let open R.Expr.Member in
    let base = transl_expr @@ base_get m in
    let field = name_get m in
    let arrow = arrow_get m in
    (* let qual_name = qual_name_get m in *) (* could be useful in the future *)
    if arrow then VF.Read (loc, base, field)
    else VF.Select (loc, base, field)

  and transl_null_ptr_lit_expr (loc: VF.loc) =
    make_int_lit loc 0

  (**************)
  (* statements *)
  (**************)

  (* TODO: redeclaration of function! *)
  and transl_decl_stmt (loc: VF.loc) (decls: (Stubs_ast.ro, R.Node.t, R.array_t) Capnp.Array.t): VF.stmt =
    let expect_var loc desc = match R.Decl.get desc with R.Decl.Var v -> Some (transl_var_decl_local loc v) | _ -> None in
    VF.DeclStmt (loc, decls |> capnp_arr_map (transl_expect expect_var))

  and transl_stmt_ann (loc: VF.loc) (text: string): VF.stmt =
    let VF.Lexed l = loc in
    AP.parse_stmt (l, text)

  and transl_compound_stmt (loc: VF.loc) (c: R.Stmt.Compound.t): VF.stmt =
    let open R.Stmt.Compound in
    let stmts = stmts_get c |> capnp_arr_map transl_stmt in
    VF.BlockStmt (loc, [], stmts, transl_loc @@ r_brace_get c, ref [])

  and transl_expr_stmt (e: R.Node.t): VF.stmt =
    VF.ExprStmt (transl_expr e)

  and transl_return_stmt (loc: VF.loc) (r: R.Stmt.Return.t): VF.stmt =
    let open R.Stmt.Return in
    let expr_opt =
      if has_expr r then Some (transl_expr @@ expr_get r)
      else None 
    in
    VF.ReturnStmt (loc, expr_opt)

  and transl_if_stmt (loc: VF.loc) (i: R.Stmt.If.t): VF.stmt =
    let open R.Stmt.If in
    let cond = transl_expr @@ cond_get i in
    let th = 
      let stmts, _ = transl_stmt_as_list @@ then_get i in 
      stmts 
    in
    let el = 
      if has_else i 
        then let stmts, _ = transl_stmt_as_list @@ else_get i in stmts
      else [] 
    in
    VF.IfStmt (loc, cond, th, el)

  and transl_null_stmt (loc: VF.loc): VF.stmt =
    VF.NoopStmt loc

  and transl_while_like (loc: VF.loc) (w: R.Stmt.While.t): VF.loc * VF.expr * VF.stmt list * VF.loop_spec option * VF.asn option =
    let open R.Stmt.While in
    let while_loc = transl_loc @@ while_loc_get w in
    let cond = transl_expr @@ cond_get w in
    let body = [transl_stmt @@ body_get w] in
    let spec, decr = spec_get w |> capnp_arr_map map_ann_clause |> AP.parse_loop_spec loc in
    while_loc, cond, body, spec, decr

  and transl_while_stmt (loc: VF.loc) (w: R.Stmt.While.t): VF.stmt =
    let _, cond, body, spec, decr = transl_while_like loc w in
    VF.WhileStmt (loc, cond, spec, decr, body, [])

  and transl_do_while_stmt (loc: VF.loc) (w: R.Stmt.While.t): VF.stmt =
    let while_loc, cond, body, spec, decr = transl_while_like loc w in
    VF.WhileStmt (loc, VF.True loc, spec, decr, body, [VF.IfStmt (while_loc, cond, [], [VF.Break while_loc])])

  and transl_break_stmt (loc: VF.loc): VF.stmt =
    VF.Break loc

  and transl_switch_stmt (loc: VF.loc) (s: R.Stmt.Switch.t): VF.stmt =
    let open R.Stmt.Switch in
    let cond = transl_expr @@ cond_get s in
    let map_case case =
      case |> transl_expect begin fun l c ->
        match R.Stmt.get c with
        | R.Stmt.Case c -> 
          let lhs = transl_expr @@ R.Stmt.Case.lhs_get c in
          let stmts, _ = 
            if R.Stmt.Case.has_stmt c then transl_stmt_as_list @@ R.Stmt.Case.stmt_get c 
            else [], VF.dummy_loc 
          in
          Some (VF.SwitchStmtClause (l, lhs, stmts))
        | R.Stmt.DefCase c -> 
          let stmts, _ = 
            if R.Stmt.DefCase.has_stmt c then transl_stmt_as_list @@ R.Stmt.DefCase.stmt_get c 
            else [], VF.dummy_loc 
          in 
          Some (VF.SwitchStmtDefaultClause (l, stmts))
        | _ -> None
      end 
    in
    let cases = cases_get s |> capnp_arr_map map_case in
    VF.SwitchStmt (loc, cond, cases)

  (*********)
  (* types *)
  (*********)

  and transl_builtin_type (loc: VF.loc) (bt: R.Type.BuiltinKind.t): VF.type_expr = 
    let make_man t = VF.ManifestTypeExpr (loc, t) in
    let open R.Type.BuiltinKind in
    let make_int signed rank =
      make_man @@ VF.Int (signed, rank) 
    in
    match bt with
    | Char      -> make_int VF.Signed @@ VF.LitRank 0
    | UChar     -> make_int VF.Unsigned @@ VF.LitRank 0
    | Short     -> make_int VF.Signed @@ VF.LitRank 1
    | UShort    -> make_int VF.Unsigned @@ VF.LitRank 1
    | Void      -> make_man VF.Void
    | Bool      -> make_man VF.Bool
    | Int       -> make_int VF.Signed int_rank
    | UInt      -> make_int VF.Unsigned int_rank
    | Long      -> make_int VF.Signed long_rank
    | ULong     -> make_int VF.Unsigned long_rank
    | LongLong  -> make_int VF.Signed @@ VF.LitRank 3
    | ULongLong -> make_int VF.Unsigned @@ VF.LitRank 3
    | _         -> error loc "Unsupported builtin type."

  and transl_pointer_type (loc: VF.loc) (ptr: R.Type.t): VF.type_expr =
    let ty = transl_type ptr in
    VF.PtrTypeExpr (loc, ty)

  and transl_pointer_loc_type (loc :VF.loc) (ptr: R.Node.t): VF.type_expr =
    let ty = transl_type_loc ptr in
    VF.PtrTypeExpr (loc, ty)

  and transl_record_type (loc: VF.loc) (r: R.Type.Record.t): VF.type_expr =
    let open R.Type.Record in
    let name = name_get r in
    match kind_get r with
    | R.RecordKind.Struc | R.RecordKind.Class -> VF.StructTypeExpr (loc, Some name, None, [])
    | R.RecordKind.Unio -> VF.UnionTypeExpr (loc, Some name, None)

  and transl_enum_type (loc: VF.loc) (name: string): VF.type_expr =
    VF.EnumTypeExpr (loc, Some name, None)

  (********************)
  (* translation unit *)
  (********************)

  let transl_err (err: R.Err.t): 'a =
    let open R.Err in
    let loc = transl_loc @@ loc_get err in
    let reason = reason_get err in
    error loc reason

  let transl_includes (includes: R.Include.t list): Cxx_fe_sig.header_type list =
    let rec transl_includes_rec incls header_names =
      match incls with
      | [] -> [], header_names
      | h :: tl -> 
        let headers, header_name = transl_include_rec h in
        let other_headers, other_header_names = transl_includes_rec tl (header_name :: header_names) in
        List.append headers other_headers, other_header_names
    and transl_include_rec incl =
      let open R.Include in
      let fd = fd_get incl in
      let path = get_fd_path fd in
      match pop_fd_decls_opt fd with
      | None -> [], path (* ignore secondary include *)
      | Some decls ->
        let loc = loc_get incl |> transl_loc in
        let file_name = file_name_get incl in
        let incl_kind = if is_angled_get incl then Lexer.AngleBracketInclude else Lexer.DoubleQuoteInclude in
        let includes = includes_get_list incl in
        let headers, header_names = transl_includes_rec includes [] in
        let ps = [VF.PackageDecl (VF.dummy_loc, "", [], decls)] in
        List.append headers [loc, (incl_kind, file_name, path), header_names, ps], path 
    in
    let headers, _ = transl_includes_rec includes [] in
    headers

  let transl_files (files: (Stubs_ast.ro, R.File.t, R.array_t) Capnp.Array.t): unit =
    Hashtbl.clear files_table;
    Hashtbl.clear decls_table;
    let transl_file file =
      let open R.File in
      let fd = fd_get file in
      let name = path_get file in
      Hashtbl.replace files_table fd name;
      let decls = decls_get file |> capnp_arr_map transl_decl |> List.flatten in
      Hashtbl.replace decls_table fd decls 
    in
    files |> capnp_arr_iter transl_file

  let transl_tu (tu: R.TU.t): Cxx_fe_sig.header_type list * VF.decl list =
    let open R.TU in
    files_get tu |> transl_files;
    let main_fd = main_fd_get tu in
    let main_decls = pop_fd_decls main_fd in
    let includes = includes_get_list tu |> transl_includes in
    includes, main_decls

  let parse_cxx_file (path: string): Cxx_fe_sig.header_type list * VF.package list =
    (* TODO: pass macros that are whitelisted *)
    let inchan, outchan, errchan = invoke_exporter path [] in
    let close_channels () =
      let _ = Unix.close_process_full (inchan, outchan, errchan) in () 
    in
    let on_error () =
      match input_fully errchan with
      | "" -> failwith "the Cxx frontend was unable to deserialize the received message."
      | s -> failwith @@ "Cxx AST exporter error:\n" ^ s 
    in
    let in_channel = stubs_ast_in_channel inchan in
    let try_deser on_receive =
      let msg = read_capnp_message in_channel in
      match msg with
      | None -> on_error ()
      | Some res -> on_receive res 
    in
    do_finally
      begin fun () ->
        try_deser @@ fun res -> 
          match res |> R.SerResult.of_message |> R.SerResult.get with
          | R.SerResult.Undefined _ -> on_error ()
          | R.SerResult.Err -> try_deser @@ fun err -> err |> R.Err.of_message |> transl_err
          | R.SerResult.Ok ->  try_deser @@ fun msg -> 
            let headers, decls = msg |> R.TU.of_message |> transl_tu in
            headers, [VF.PackageDecl (VF.dummy_loc, "", [], decls)]
      end
      begin fun () ->
        close_channels ()
      end

end