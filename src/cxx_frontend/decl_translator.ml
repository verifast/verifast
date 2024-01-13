module R = Reader.R
module D = R.Decl

module type Translator = sig
  val translate : R.Node.t -> Ast.decl list
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  module Expr_translator = Expr_translator.Make (Node_translator)
  module Stmt_translator = Stmt_translator.Make (Node_translator)
  module Type_translator = Type_translator.Make (Node_translator)
  module Var_translator = Var_translator.Make (Node_translator)
  module AP = Node_translator.Annotation_parser

  let translate_param (param : R.Param.t) : Ast.type_expr * string =
    let open R.Param in
    if has_default param then
      failwith "Parameters with default expressions are not supported yet."
    else (type_get param |> Type_translator.translate, name_get param)

  let rec translate_decomposed loc decl_desc =
    if D.is_implicit_get decl_desc then []
    else
      match D.get decl_desc with
      | UnionNotInitialized -> Error.union_no_init_err "declaration"
      | Empty -> []
      | Function f -> [ transl_func_decl loc f ]
      | Ann a -> transl_ann_decls loc a
      | Record r -> transl_record_decl loc r
      | Method m -> [ transl_meth_decl loc m ]
      | Var v -> [ transl_var_decl_global loc v ]
      | EnumDecl d -> [ transl_enum_decl loc d ]
      | Typedef d -> [ transl_typedef_decl loc d ]
      | Ctor c -> [ transl_ctor_decl loc c false ]
      | Dtor d -> [ transl_dtor_decl loc d false ]
      | AccessSpec -> [] (* TODO: don't ignore this? *)
      | Namespace ns -> transl_namespace_decl loc ns
      | FunctionTemplate ft -> transl_function_template_decl loc ft
      | Undefined _ -> failwith "Undefined declaration."
      | _ -> Error.error loc "Unsupported declaration."

  and translate decl_node =
    Node_translator.map ~f:translate_decomposed decl_node

  and transl_func (loc : Ast.loc) (f : D.Function.t) =
    let open D.Function in
    let name = name_get f in
    let body_opt =
      if has_body f then Some (Stmt_translator.expect_compund_stmt @@ body_get f)
      else None
    in
    let ng_callers_only, ft, pre_post, terminates =
      contract_get f
      |> Capnp_util.arr_map Node_translator.map_annotation
      |> AP.parse_func_contract loc
    in
    let return_type = result_get f |> Type_translator.translate_return_type in
    let params = params_get f |> Capnp_util.arr_map translate_param in
    ( name,
      params,
      body_opt,
      (ng_callers_only, ft, pre_post, terminates),
      return_type )

  and transl_func_decl (loc : Ast.loc) (f : D.Function.t) : Ast.decl =
    let ( name,
          params,
          body_opt,
          (ng_callers_only, ft, pre_post, terminates),
          return_type ) =
      transl_func loc f
    in
    let make_return loc =
      Ast.ReturnStmt (loc, Some (Expr_translator.make_int_lit loc 0))
    in
    let name, body_stmts =
      match (name, body_opt) with
      | "main()", Some ([], l) -> ("main", Some ([ make_return l ], l))
      | "main()", Some (body, l) ->
          ( "main",
            match List.rev body with
            | Ast.ReturnStmt _ :: _ -> body_opt
            | _ -> Some (body @ [ make_return l ], l) )
      | _ -> (name, body_opt)
    in
    Ast.Func
      ( loc,
        Ast.Regular,
        [],
        return_type,
        name,
        params,
        ng_callers_only,
        ft,
        pre_post,
        terminates,
        body_stmts,
        false,
        [] )

  and transl_ann_decls (loc : Ast.loc) (text : string) : Ast.decl list =
    let (Ast.Lexed l) = loc in
    AP.parse_decls (l, text)

  and transl_var_init (i : D.Var.VarInit.t) : Ast.expr =
    let open D.Var.VarInit in
    let init_expr = init_get i |> Expr_translator.translate in
    match style_get i with
    | D.Var.InitStyle.ListInit ->
        Error.error (Ast.expr_loc init_expr)
          "List initialization is not supported yet."
    | _ -> init_expr

  (* used at global level, i.e., outside functions, methods... *)
  and transl_var_decl_global (loc : Ast.loc) (var : D.Var.t) : Ast.decl =
    let ty, name, init_opt = Var_translator.translate var in
    Ast.Global (loc, ty, name, init_opt)

  (* every declaration in the record that is not a field is translated as a separate declaration *)
  and transl_record_decl (loc : Ast.loc) (record : D.Record.t) : Ast.decl list =
    let open D.Record in
    let name = name_get record in
    let transl_mems (decls : R.Node.t list) : Sig.struct_member_decl list =
      let transl_mem decl =
        let loc, desc = Node_translator.decompose decl in
        match D.get desc with
        | D.Ann ann ->
            let (Ast.Lexed l) = loc in
            AP.parse_struct_members name (l, ann)
        | D.Field f ->
            let field = transl_field_decl loc f in
            [ Sig.CxxFieldMem field ]
        | _ -> translate decl |> List.map (fun d -> Sig.CxxDeclMem d)
      in
      decls |> Util.flatmap transl_mem
    in
    let body, decls =
      if has_body record then
        let open Body in
        let transl_base loc desc =
          let open BaseSpec in
          Ast.CxxBaseSpec (loc, name_get desc, virtual_get desc)
        in
        let body = body_get record in
        match (is_abstract_get body, non_overridden_methods_get_list body) with
        | false, meth :: _ ->
            Error.error loc
              ("This record must override virtual method '" ^ meth
             ^ "' or must be abstract.")
        | _ ->
            let polymorphic = polymorphic_get body in
            let mems = body |> decls_get_list |> transl_mems in
            let decls, fields, inst_preds =
              mems
              |> List.fold_left
                   (fun (decls, fields, inst_preds) mem ->
                     match mem with
                     | Sig.CxxFieldMem field ->
                         (decls, field :: fields, inst_preds)
                     | Sig.CxxInstPredMem pred ->
                         (decls, fields, pred :: inst_preds)
                     | Sig.CxxDeclMem
                         (Ast.Func
                           (l, Lemma _, _, _, _, _, _, _, _, _, _, _, _)) ->
                         Error.error l
                           "Lemmas are not supported inside struct or class \
                            declarations."
                     | Sig.CxxDeclMem decl -> (decl :: decls, fields, inst_preds))
                   ([], [], [])
            in
            let bases =
              bases_get body
              |> Capnp_util.arr_map (Node_translator.map ~f:transl_base)
            in
            ( Some
                ( List.rev bases,
                  List.rev fields,
                  List.rev inst_preds,
                  polymorphic ),
              List.rev decls )
      else (None, [])
    in
    let vf_record =
      match kind_get record with
      | R.RecordKind.Struc | R.RecordKind.Class ->
          Ast.Struct (loc, name, body, [])
      | R.RecordKind.Unio ->
          Ast.Union
            (loc, name, body |> Option.map @@ fun (_, fields, _, _) -> fields)
    in
    vf_record :: decls

  and transl_meth (loc : Ast.loc) (meth : D.Method.t) =
    let open D.Method in
    let name, params, body_opt, anns, return_type =
      func_get meth |> transl_func loc
    in
    let is_static = static_get meth in
    let params =
      if is_static then params
      else
        let this_type =
          this_get meth |> Type_translator.translate_decomposed loc
        in
        (Ast.PtrTypeExpr (Ast.dummy_loc, this_type), "this") :: params
    in
    let is_virtual = virtual_get meth in
    let overrides =
      if has_overrides meth then
        let open Override in
        overrides_get meth
        |> Capnp_util.arr_map (fun ov ->
               let mangled_name = name_get ov in
               let (Ast.StructType base) =
                 base_get ov |> transl_record_ref loc
               in
               (base, mangled_name))
      else []
    in
    (name, params, body_opt, anns, return_type, is_virtual, overrides)

  (* translates a method to a function and prepends 'this' to the parameters in case it is not a static method *)
  and transl_meth_decl (loc : Ast.loc) (meth : D.Method.t) : Ast.decl =
    let open D.Method in
    let ( name,
          params,
          body_opt,
          (ng_callers_only, ft, pre_post, terminates),
          return_type,
          is_virtual,
          overrides ) =
      transl_meth loc meth
    in
    Ast.Func
      ( loc,
        Ast.Regular,
        [],
        return_type,
        name,
        params,
        ng_callers_only,
        ft,
        pre_post,
        terminates,
        body_opt,
        is_virtual,
        overrides |> List.map snd )

  and transl_record_ref (loc : Ast.loc) (record_ref : R.RecordRef.t) : Ast.type_
      =
    let open R.RecordRef in
    let name = name_get record_ref in
    match kind_get record_ref with
    | R.RecordKind.Struc | R.RecordKind.Class -> Ast.StructType name
    | R.RecordKind.Unio -> Ast.UnionType name
    | _ -> Error.error loc "Invalid record reference"

  and transl_ctor_decl (loc : Ast.loc) (ctor : D.Ctor.t) (implicit : bool) :
      Ast.decl =
    let open D.Ctor in
    let ( name,
          this_param :: params,
          body_opt,
          (_, _, pre_post_opt, terminates),
          _,
          _,
          _ ) =
      method_get ctor |> transl_meth loc
    in
    (* the init list also contains member names that are default initialized and don't appear in the init list *)
    (* in that case, no init expr is present (we can always retrieve it from the field default initializer) *)
    let transl_init init =
      let open CtorInit in
      ( name_get init,
        if has_init init then
          Some (init_get init |> Expr_translator.translate, is_written_get init)
        else None )
    in
    let body_opt =
      body_opt
      |> Option.map @@ fun body ->
         let init_list = init_list_get ctor |> Capnp_util.arr_map transl_init in
         (init_list, body)
    in
    let parent = ctor |> parent_get |> transl_record_ref loc in
    Ast.CxxCtor
      (loc, name, params, pre_post_opt, terminates, body_opt, implicit, parent)

  and transl_dtor_decl (loc : Ast.loc) (dtor : D.Dtor.t) (implicit : bool) :
      Ast.decl =
    let open D.Dtor in
    let ( name,
          [ this_param ],
          body_opt,
          (_, _, pre_post_opt, terminates),
          _,
          is_virtual,
          overrides ) =
      method_get dtor |> transl_meth loc
    in
    let parent = dtor |> parent_get |> transl_record_ref loc in
    Ast.CxxDtor
      ( loc,
        name,
        pre_post_opt,
        terminates,
        body_opt,
        implicit,
        parent,
        is_virtual,
        overrides |> List.map fst )

  and transl_field_decl (loc : Ast.loc) (field : D.Field.t) : Ast.field =
    let open D.Field in
    let name = name_get field in
    let ty = type_get field |> Type_translator.translate in
    let init_opt =
      if has_init field then
        let init = init_get field in
        let open FieldInit in
        let init_expr = init_get init |> Expr_translator.translate in
        match style_get init with
        | InitStyle.CopyInit -> Some init_expr
        | _ ->
            Error.error loc
              "Only copy initialization is supported at the moment."
      else None
    in
    Ast.Field
      (loc, Ast.Real, ty, name, Ast.Instance, Ast.Public, false, init_opt)

  and transl_enum_decl (loc : Ast.loc) (decl : D.Enum.t) : Ast.decl =
    let open D.Enum in
    let name = name_get decl in
    let transl_enum_field field =
      let name = EnumField.name_get field in
      let expr_opt =
        if EnumField.has_expr field then
          Some (Expr_translator.translate @@ EnumField.expr_get field)
        else None
      in
      (name, expr_opt)
    in
    let fields = fields_get decl |> Capnp_util.arr_map transl_enum_field in
    Ast.EnumDecl (loc, name, fields)

    and transl_function_proto_type (loc: Ast.loc) (proto_type: R.Type.FunctionProto.t): Ast.type_expr option * (string list * (Ast.type_expr * string) list * (Ast.type_expr * string) list) * (Ast.asn * Ast.asn * bool) =
      let open R.Type.FunctionProto in
      let return_type = return_type_get proto_type |> Type_translator.translate_return_type in
      let params = params_get proto_type |> Capnp_util.arr_map translate_param in
      let contract = contract_get proto_type |> Capnp_util.arr_map Node_translator.map_annotation |> AP.parse_functype_contract loc in
      let functype_type_params, functype_params = 
        let ann = ghost_params_get proto_type |> Capnp_util.arr_map Node_translator.map_annotation in
        match ann with
        | [] -> [], []
        | [ann] -> AP.parse_functype_ghost_params ann
        | _ -> Error.error loc @@ "A single annotation expected of the form '/*@ ... @*/'."
      in
      return_type, (functype_type_params, functype_params, params), contract

  and transl_typedef_decl (loc : Ast.loc) (decl : D.Typedef.t) : Ast.decl =
    let open D.Typedef in
    let name = name_get decl in
    let l, type_desc = type_get decl |> Node_translator.decompose in
    match R.Type.get type_desc with
    | R.Type.FunctionProto fp ->
        let return_type, (ft_type_params, ft_params, params), contract =
          transl_function_proto_type l fp
        in
        Ast.FuncTypeDecl
          ( loc,
            Ast.Real,
            return_type,
            name,
            ft_type_params,
            ft_params,
            params,
            contract )
    | _ ->
        let ty = Type_translator.translate_decomposed l type_desc in
        Ast.TypedefDecl (loc, ty, name)

  (* TODO: we currnetly ignore the name, because the serializer exposes qualified names.
     However, namespaces might be useful to scope ghost code. *)
  and transl_namespace_decl (loc : Ast.loc) (decl : D.Namespace.t) :
      Ast.decl list =
    let open D.Namespace in
    (* let name = name_get decl in *)
    decls_get decl |> Capnp_util.arr_map translate |> List.flatten

  and transl_function_template_decl (loc : Ast.loc)
      (decl : D.FunctionTemplate.t) : Ast.decl list =
    let open D.FunctionTemplate in
    (* let name = name_get decl in *)
    let ng_callers_only, ft, pre_post, terminates =
      contract_get decl
      |> Capnp_util.arr_map Node_translator.map_annotation
      |> AP.parse_func_contract loc
    in
    let transl_spec loc desc =
      let name, params, body_opt, _, return_type = transl_func loc desc in
      Ast.Func
        ( loc,
          Ast.Regular,
          [],
          return_type,
          name,
          params,
          ng_callers_only,
          ft,
          pre_post,
          terminates,
          body_opt,
          false,
          [] )
    in
    specs_get decl |> Capnp_util.arr_map (Node_translator.map ~f:transl_spec)
end
