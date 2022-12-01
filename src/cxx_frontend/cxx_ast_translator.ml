module Stubs = Stubs_ast.Make(Capnp.BytesMessage)
module R = Stubs.Reader
module VF = Ast
open Util
open Big_int

type 'a capnp_arr = (Stubs_ast.ro, 'a, R.array_t) Capnp.Array.t

(**
  [capnp_arr_map f arr] applies [f] to every element of cap'n proto array [arr] and return a new list containing those elements.
*)
let capnp_arr_map (f: 'a -> 'b) (arr: 'a capnp_arr): 'b list =
  (* map array to list first, the map function of capnp traverses the array in reverse order *)
  arr |> Capnp.Array.to_list |> List.map f

(**
  [capnp_arr_iter] applies [f] to every element of cap'n proto array [arr].
*)
let capnp_arr_iter (f: 'a -> 'b) (arr: 'a capnp_arr): unit =
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
    The next message that is transmitted through {i in_channel} represents the serialized C++ AST.

    Otherwise a message {i SerResult.Error} is transmitted through {i error_channel}
    if any error occurred during compilation, context free macro expansion checking, or AST serialization.
    This error message contains an explanation why the C++ AST exporter produced an error.
  *)
  let invoke_exporter (file: string) (allow_expansions: string list) =
    let bin_dir = Filename.dirname Sys.executable_name in
    let frontend_macro = "__VF_CXX_CLANG_FRONTEND__" in
    let allow_expansions = frontend_macro :: allow_expansions in
    (* 
      -allow_macro_expansion=<expansions>   Don't check context-free expasions for <expansions>
      -x<language>                          Treat input files as having type <language> 
      -I<dir>                               Include dir
      -D<macros>                            Define macros <macros>
    *)
    let cmd = 
      Printf.sprintf "%s/vf-cxx-ast-exporter %s -allow_macro_expansion=%s -- -x%s -I%s -D%s %s" 
      bin_dir 
      file 
      (String.concat "," allow_expansions) 
      (match Args.dialect_opt with Some Cxx -> "c++" | _ -> "c")
      bin_dir 
      frontend_macro
      (Args.include_paths |> List.map (fun s -> "-I" ^ s) |> String.concat " ")
    in
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
    and a cap'n proto pointer pointing to the description of [node].
  *)
  let decompose_node (node: R.Node.t): VF.loc * 'a Stubs.reader_t =
    let open R.Node in
    let loc = if has_loc node then loc_get node |> transl_loc else VF.dummy_loc in
    let desc = desc_get node in
    loc, R.of_pointer desc

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

  let method_is_implicit (meth: R.Decl.Method.t): bool =
    R.Decl.Method.implicit_get meth

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
    | Method m            -> if method_is_implicit m then [] else [transl_meth_decl loc m]
    | Var v               -> [transl_var_decl_global loc v]
    | EnumDecl d          -> [transl_enum_decl loc d]
    | Typedef d           -> [transl_typedef_decl loc d]
    | Ctor c              -> if R.Decl.Ctor.method_get c |> method_is_implicit then [] else [transl_ctor_decl loc c]
                              (* TODO: we currently skip implicit constructors *)
    | Dtor d              -> if R.Decl.Dtor.method_get d |> method_is_implicit then [] else [transl_dtor_decl loc d]
                              (* TODO: skipping implicit dtors *)
    | AccessSpec          -> []  (* TODO: don't ignore this? *)   
    | Namespace ns        -> transl_namespace_decl loc ns
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
    | MemberCall c        -> transl_member_call_expr loc c
    | NullPtrLit          -> transl_null_ptr_lit_expr loc
    | Delete d            -> transl_delete_expr loc d
    | Truncating t        -> transl_trunc_expr loc t
    | LValueToRValue l    -> transl_lvalue_to_rvalue_expr loc l
    | DerivedToBase e     -> transl_derived_to_base_expr loc e
    | OperatorCall o      -> transl_operator_call_expr loc o
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

  and transl_type (loc: VF.loc) (ty: R.Type.t): VF.type_expr = 
    let open R.Type in
    match get ty with 
      | UnionNotInitialized -> union_no_init_err "type"
      | Builtin b           -> transl_builtin_type loc b 
      | Pointer p           -> transl_pointer_type loc p
      | Record r            -> transl_record_type loc r 
      | EnumType e          -> transl_enum_type loc e 
      | Elaborated e        -> transl_elaborated_type e
      | Typedef t           -> transl_typedef_type loc t
      | FixedWidth f        -> transl_fixed_width_type loc f
      | LValueRef l         -> transl_lvalue_ref_type loc l
      | Undefined _         -> failwith "Undefined type."
      | _                   -> error loc "Unsupported type."
      
  (**
    [transl_type_loc ty] translates [ty] and returns a VeriFast type expression, representing [ty].
  *)
  and transl_type_loc (type_node: R.Node.t): VF.type_expr =
    let loc, desc = decompose_node type_node in
    transl_type loc desc

  (****************)
  (* declarations *)
  (****************)

  and transl_param (param: R.Param.t): VF.type_expr * string =
    let open R.Param in
    if has_default param then failwith "Parameters with default expressions are not supported yet."
    else type_get param |> transl_type_loc, name_get param 

  and transl_return_type (type_node: R.Node.t): VF.type_expr option =
    match transl_type_loc type_node with
    | VF.ManifestTypeExpr (_, VF.Void) -> None
    | rt -> Some rt 

  and transl_func (loc: VF.loc) (f: R.Decl.Function.t) = 
    let open R.Decl.Function in
    let name = name_get f in
    let mangled_name = mangled_name_get f in 
    let body_opt = 
      if has_body f then Some (transl_stmt_as_list @@ body_get f)
      else None 
    in
    let ng_callers_only, ft, pre_post, terminates = contract_get f |> capnp_arr_map map_ann_clause |> AP.parse_func_contract loc in
    let return_type = result_get f |> transl_return_type in
    let params = params_get f |> capnp_arr_map transl_param in
    name, mangled_name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type

  and transl_func_decl (loc: VF.loc) (f: R.Decl.Function.t): VF.decl =
    let _, name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type = transl_func loc f in
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
    VF.Func (loc, VF.Regular, [], return_type, name, params, ng_callers_only, ft, pre_post, terminates, body_stmts, false, [])

  and transl_ann_decls (loc: VF.loc) (text: string): VF.decl list =
    let VF.Lexed l = loc in
    AP.parse_decls (l, text)

  and transl_var_init (i: R.Decl.Var.VarInit.t): VF.expr =
    let open R.Decl.Var.VarInit in
    let init_expr = init_get i |> transl_expr in 
    match style_get i with 
    | R.Decl.Var.InitStyle.ListInit -> error (VF.expr_loc init_expr) "List initialization is not supported yet."
    | _ -> init_expr

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
    let transl_mems (decls: R.Node.t list): Cxx_fe_sig.struct_member_decl list =
      let transl_mem decl =
        let loc, desc = decompose_node decl in
        match R.Decl.get desc with
        | R.Decl.Ann ann ->
          let VF.Lexed l = loc in
          AP.parse_struct_members name (l, ann)
        | R.Decl.Field f ->
          let field = transl_field_decl loc f in
          [Cxx_fe_sig.CxxFieldMem field]
        | _ ->
          transl_decl decl |> List.map (fun d -> Cxx_fe_sig.CxxDeclMem d)
      in
      decls |> flatmap transl_mem
    in
    let body, decls = 
      if has_body record then
        let open Body in
        let transl_base loc desc =
          let open BaseSpec in
          VF.CxxBaseSpec (loc, name_get desc, virtual_get desc)
        in
        let body = body_get record in
        let polymorphic = polymorphic_get body in
        let mems = body |> decls_get_list |> transl_mems in
        let decls, fields, inst_preds =
          mems |> List.fold_left (fun (decls, fields, inst_preds) mem ->
            match mem with
            | Cxx_fe_sig.CxxFieldMem (VF.Field (l, Ghost, _, _, _, _, _, _)) ->
              error l "Ghost fields are not supported."
            | Cxx_fe_sig.CxxFieldMem field ->
              decls, field :: fields, inst_preds
            | Cxx_fe_sig.CxxInstPredMem (VF.InstancePredDecl (l, _, _, _)) ->
              error l "Instance predicates are not supported."
            | Cxx_fe_sig.CxxDeclMem (VF.Func (l, Lemma _, _, _, _, _, _, _, _, _, _, _, _)) ->
              error l "Lemmas are notsupported inside struct or class declarations."
            | Cxx_fe_sig.CxxDeclMem decl ->
              decl :: decls, fields, inst_preds) ([], [], [])
        in
        let bases = bases_get body |> capnp_arr_map (transl_node transl_base) in
        Some (List.rev bases, List.rev fields, polymorphic), List.rev decls
      else None, [] 
    in
    let vf_record = 
      match kind_get record with
      | R.RecordKind.Struc | R.RecordKind.Class -> 
        VF.Struct (loc, name, body, []) 
      | R.RecordKind.Unio -> 
        VF.Union (loc, name, body |> option_map @@ fun (_, fields, _) -> fields) 
    in
    vf_record :: decls

  and transl_meth (loc: VF.loc) (meth: R.Decl.Method.t) =
    let open R.Decl.Method in
    let name, mangled_name, params, body_opt, anns, return_type = func_get meth |> transl_func loc in
    let is_static = static_get meth in
    let params = 
      if is_static then params
      else 
        let this_type = this_get meth |> transl_type loc in
        (VF.PtrTypeExpr (VF.dummy_loc, this_type), "this") :: params 
    in
    let implicit = implicit_get meth in
    let is_virtual = virtual_get meth in
    let overrides = 
      if has_overrides meth then overrides_get_list meth
      else []
    in
    name, mangled_name, params, body_opt, anns, return_type, implicit, is_virtual, overrides

  (* translates a method to a function and prepends 'this' to the parameters in case it is not a static method *)
  and transl_meth_decl (loc: VF.loc) (meth: R.Decl.Method.t): VF.decl =
    let open R.Decl.Method in
    let _, mangled_name, params, body_opt, (ng_callers_only, ft, pre_post, terminates), return_type, _, is_virtual, overrides = transl_meth loc meth in
    VF.Func (loc, VF.Regular, [], return_type, mangled_name, params, ng_callers_only, ft, pre_post, terminates, body_opt, is_virtual, overrides)

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
    let _, mangled_name, this_param :: params, body_opt, (_, _, pre_post_opt, terminates), _, implicit, _, _ = method_get ctor |> transl_meth loc in
    (* the init list also contains member names that are default initialized and don't appear in the init list *)
    (* in that case, no init expr is present (we can always retrieve it from the field default initializer) *)
    let transl_init init =
      let open CtorInit in
      name_get init, if has_init init then Some (init_get init |> transl_expr, is_written_get init) else None in
    let body_opt = body_opt |> option_map @@ fun body ->
      let init_list = init_list_get ctor |> capnp_arr_map transl_init in
      init_list, body in
    let parent = ctor |> parent_get |> transl_record_ref loc in
    VF.CxxCtor (loc, mangled_name, params, pre_post_opt, terminates, body_opt, implicit, parent)

  and transl_dtor_decl (loc: VF.loc) (dtor: R.Decl.Dtor.t): VF.decl =
    let open R.Decl.Dtor in 
    let _, _, [this_param], body_opt, (_, _, pre_post_opt, terminates), _, implicit, is_virtual, overrides = method_get dtor |> transl_meth loc in
    let parent = dtor |> parent_get |> transl_record_ref loc in
    VF.CxxDtor (loc, pre_post_opt, terminates, body_opt, implicit, parent)

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
    let l, type_desc = type_get decl |> decompose_node in
    match R.Type.get type_desc with
    | R.Type.FunctionProto fp ->
      let return_type, (ft_type_params, ft_params, params), contract = transl_function_proto_type l fp in
      VF.FuncTypeDecl (loc, VF.Real, return_type, name, ft_type_params, ft_params, params, contract)
    | _ -> 
      let ty = transl_type l type_desc in
      VF.TypedefDecl (loc, ty, name)

  (* TODO: we currnetly ignore the name, because the serializer exposes qualified names.
     However, namespaces might be useful to scope ghost code. *)
  and transl_namespace_decl (loc: VF.loc) (decl: R.Decl.Namespace.t): VF.decl list =
    let open R.Decl.Namespace in
    (* let name = name_get decl in *)
    decls_get decl |> capnp_arr_map transl_decl |> List.flatten

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

  and map_args (args: R.Node.t capnp_arr): VF.pat list =
    args |> capnp_arr_map (fun e -> VF.LitPat (transl_expr e))

  and transl_call (loc: VF.loc) (call: R.Expr.Call.t): string * VF.pat list =
  let open R.Expr.Call in
  let callee = callee_get call in
  let args = args_get call |> map_args in
  let name =
    let callee_loc, desc = decompose_node callee in
    let e = R.Expr.get desc in
    match e with
    | R.Expr.DeclRef r -> (* c-like function call, operator calls (even tho they can be class methods) *)
      R.Expr.DeclRef.mangled_name_get r
    | R.Expr.Member m ->  (* C++ method call on explicit or implicit (this) object *)
      R.Expr.Member.mangled_name_get m 
    | _ -> error loc "Unsupported callee in function or method call." 
  in
  name, args

  and transl_call_expr (loc: VF.loc) (call: R.Expr.Call.t): VF.expr =
    let name, args = transl_call loc call in
    VF.CallExpr (loc, name, [], [], args, VF.Static)

  and transl_operator_call_expr (loc: VF.loc) (call: R.Expr.Call.t): VF.expr =
    let name, VF.LitPat this_arg :: args = transl_call loc call in
    let args = VF.LitPat (VF.make_addr_of (VF.expr_loc this_arg) this_arg) :: args in
    VF.CallExpr (loc, name, [], [], args, VF.Static)

  and transl_member_call_expr (loc: VF.loc) (member_call: R.Expr.MemberCall.t): VF.expr =
    let open R.Expr.MemberCall in
    let name, args = call_get member_call |> transl_call loc in
    let impl_arg = 
      let arg = implicit_arg_get member_call |> transl_expr in
      if arrow_get member_call then arg else VF.make_addr_of (VF.expr_loc arg) arg
    in
    let args = VF.LitPat impl_arg :: args in
    let binding = if target_has_qualifier_get member_call then VF.Static else VF.Instance in
    VF.CallExpr (loc, name, [], [], args, binding)

  and transl_decl_ref_expr (loc: VF.loc) (ref: R.Expr.DeclRef.t): VF.expr =
    VF.Var (loc, R.Expr.DeclRef.name_get ref)

  and transl_this_expr (loc: VF.loc): VF.expr =
    VF.Var (loc, "this")

  and transl_construct_expr (loc: VF.loc) (c: R.Expr.Construct.t): VF.expr =
    let open R.Expr.Construct in 
    let mangled_name = mangled_name_get c in
    let ty = type_get c |> transl_type loc in
    let args = args_get c |> capnp_arr_map transl_expr in
    VF.CxxConstruct (loc, mangled_name, ty, args)

  and transl_new_expr (loc: VF.loc) (n: R.Expr.New.t): VF.expr =
    let open R.Expr.New in
    let expr_opt = 
      if has_expr n then Some (expr_get n |> transl_expr)
      else None
    in
    let ty = type_get n |> transl_type loc in
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

  and transl_trunc_expr (loc: VF.loc) (t: R.Node.t): VF.expr =
    let e = transl_expr t in
    VF.TruncatingExpr (loc, e)

  and transl_lvalue_to_rvalue_expr (loc: VF.loc) (e: R.Node.t): VF.expr =
    let e = transl_expr e in
    VF.CxxLValueToRValue (loc, e)

  and transl_derived_to_base_expr (loc: VF.loc) (e: R.Expr.StructToStruct.t): VF.expr =
    let open R.Expr.StructToStruct in 
    let sub_expr = expr_get e |> transl_expr in
    let ty = type_get e |> transl_type loc in
    VF.CxxDerivedToBase (loc, sub_expr, ty)

  (**************)
  (* statements *)
  (**************)

  (* TODO: redeclaration of function! *)
  and transl_decl_stmt (loc: VF.loc) (decls: R.Node.t capnp_arr): VF.stmt =
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
    | Char      -> make_int VF.Signed @@ VF.CharRank
    | UChar     -> make_int VF.Unsigned @@ VF.CharRank
    | Short     -> make_int VF.Signed @@ VF.ShortRank
    | UShort    -> make_int VF.Unsigned @@ VF.ShortRank
    | Void      -> make_man VF.Void
    | Bool      -> make_man VF.Bool
    | Int       -> make_int VF.Signed IntRank
    | UInt      -> make_int VF.Unsigned IntRank
    | Long      -> make_int VF.Signed LongRank
    | ULong     -> make_int VF.Unsigned LongRank
    | LongLong  -> make_int VF.Signed @@ LongLongRank
    | ULongLong -> make_int VF.Unsigned @@ LongLongRank
    | _         -> error loc "Unsupported builtin type."

  and transl_pointer_type (loc: VF.loc) (ptr: R.Node.t): VF.type_expr = 
    let pointee_type = transl_type_loc ptr in
    VF.PtrTypeExpr (loc, pointee_type)

  and transl_lvalue_ref_type (loc: VF.loc) (l: R.Node.t): VF.type_expr =
    let ref_type = transl_type_loc l in
    VF.LValueRefTypeExpr (loc, ref_type)

  and transl_elaborated_type (e: R.Node.t): VF.type_expr =
    transl_type_loc e

  and transl_typedef_type (loc: VF.loc) (id: string): VF.type_expr =
    VF.IdentTypeExpr (loc, None, id)

  and transl_record_type (loc: VF.loc) (r: R.RecordRef.t): VF.type_expr =
    let open R.RecordRef in
    let name = name_get r in
    match kind_get r with
    | R.RecordKind.Struc | R.RecordKind.Class -> VF.StructTypeExpr (loc, Some name, None, [])
    | R.RecordKind.Unio -> VF.UnionTypeExpr (loc, Some name, None)

  and transl_enum_type (loc: VF.loc) (name: string): VF.type_expr =
    VF.EnumTypeExpr (loc, Some name, None)

  and transl_fixed_width_type (loc: VF.loc) (fw: R.Type.FixedWidth.t): VF.type_expr =
    let open R.Type.FixedWidth in
    let rank = 
      match bits_get fw with
      | 8 ->  VF.FixedWidthRank 0
      | 16 -> VF.FixedWidthRank 1
      | 32 -> VF.FixedWidthRank 2
      | 64 -> VF.FixedWidthRank 3
      | 128 -> VF.FixedWidthRank 4
      | n -> error loc @@ "Invalid fixed width specified in type: " ^ (string_of_int n)
    in
    let signed = 
      match kind_get fw with
      | FixedWidthKind.Int -> VF.Signed
      | FixedWidthKind.UInt -> VF.Unsigned 
    in
    ManifestTypeExpr (loc, VF.Int (signed, rank))

  and transl_function_proto_type (loc: VF.loc) (proto_type: R.Type.FunctionProto.t): VF.type_expr option * (string list * (VF.type_expr * string) list * (VF.type_expr * string) list) * (VF.asn * VF.asn * bool) =
    let open R.Type.FunctionProto in
    let return_type = return_type_get proto_type |> transl_return_type in
    let params = params_get proto_type |> capnp_arr_map transl_param in
    let contract = contract_get proto_type |> capnp_arr_map map_ann_clause |> AP.parse_functype_contract loc in
    let functype_type_params, functype_params = 
      let ann = ghost_params_get proto_type |> capnp_arr_map map_ann_clause in
      match ann with
      | [] -> [], []
      | [ann] -> AP.parse_functype_ghost_params ann
      | _ -> error loc @@ "A single annotation expected of the form '/*@ ... @*/'."
    in
    return_type, (functype_type_params, functype_params, params), contract

  (********************)
  (* translation unit *)
  (********************)

  let transl_err (err: R.Err.t): 'a =
    let open R.Err in
    let loc = transl_loc @@ loc_get err in
    let reason = reason_get err in
    error loc reason

  let transl_includes (decls_map: (int * R.Node.t capnp_arr) list) (includes: R.Include.t list): Cxx_fe_sig.header_type list =
    let active_headers = ref [] in
    let test_include_cycle l path =
      if List.mem path !active_headers then raise (Lexer.ParseException (l, "Include cycles (even with header guards) are not supported"));
    in
    let add_active_header path =
      active_headers := path :: !active_headers
    in
    let remove_active_header path =
      active_headers := List.filter (fun h -> h <> path) !active_headers;
    in
    let transl_decls fd = List.assoc fd decls_map |> capnp_arr_map transl_decl |> List.flatten in
    let open R.Include in
    let rec transl_includes_rec path incls header_names all_includes_done_paths =
      match incls with
      | [] -> [], header_names
      | h :: tl -> 
        match get h with
        | RealInclude incl ->
          let headers, header_name = transl_real_include_rec incl all_includes_done_paths in
          let other_headers, other_header_names = transl_includes_rec path tl (header_name :: header_names) (header_name :: all_includes_done_paths) in
          List.append headers other_headers, other_header_names
        | GhostInclude incl ->
          let ann = map_ann_clause incl in
          let included_files_ref = ref all_includes_done_paths in
          let ghost_headers, ghost_header_names = AP.parse_include_directives path ann active_headers included_files_ref in
          let other_headers, other_header_names = transl_includes_rec path tl (List.append ghost_header_names header_names) !included_files_ref in
          List.append ghost_headers other_headers, other_header_names
    and transl_real_include_rec incl all_includes_done_paths =
      let open RealInclude in
      let file_name = file_name_get incl in
      let path = abs_path file_name in
      let fd = fd_get incl in
      let loc = loc_get incl |> transl_loc in
      if List.mem path all_includes_done_paths then
        let () = test_include_cycle loc path in
        [], path
      else
        let incl_kind = if is_angled_get incl then Lexer.AngleBracketInclude else Lexer.DoubleQuoteInclude in
        let includes = includes_get_list incl in
        let () = add_active_header path in
        let headers, header_names = transl_includes_rec path includes [] (path :: all_includes_done_paths) in
        let () = remove_active_header path in
        let decls = transl_decls fd in
        let ps = [VF.PackageDecl (VF.dummy_loc, "", [], decls)] in
        List.append headers [loc, (incl_kind, file_name, path), header_names, ps], path
    in
    let headers, _ = transl_includes_rec Args.path includes [] [] in
    headers

  let transl_files (files: R.File.t capnp_arr): (int * R.Node.t capnp_arr) list =
    Hashtbl.clear files_table;
    let transl_file file =
      let open R.File in
      let fd = fd_get file in
      let name = path_get file in
      Hashtbl.replace files_table fd name;
      let decls = decls_get file in
      fd, decls
    in
    files |> capnp_arr_map transl_file

  let transl_tu (tu: R.TU.t): Cxx_fe_sig.header_type list * VF.decl list =
    let open R.TU in
    let decls_table = files_get tu |> transl_files in
    let includes = includes_get_list tu |> transl_includes decls_table in
    let main_fd = main_fd_get tu in
    let main_decls = List.assoc main_fd decls_table |> capnp_arr_map transl_decl |> List.flatten in
    let () = fail_directives_get tu |> capnp_arr_map map_ann_clause |> List.iter @@ fun (l, s) -> Args.report_should_fail s l in
    includes, main_decls

  let parse_cxx_file (): Cxx_fe_sig.header_type list * VF.package list =
    (* TODO: pass macros that are whitelisted *)
    let type_macros pref =
      [8; 16; 32; 64] |> List.map @@ fun n ->
        Printf.sprintf "__%s%u_TYPE__" pref n
    in
    let enable_types = 
      type_macros "INT" @ type_macros "UINT"
    in
    let inchan, outchan, errchan = invoke_exporter Args.path enable_types in
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
