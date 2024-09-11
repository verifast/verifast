module R = Reader.R
module T = R.Type

module type Translator = sig
  val translate_decomposed : Ast.loc -> T.t -> Ast.type_expr
  val translate : R.Node.t -> Ast.type_expr
  val translate_return_type : R.Node.t -> Ast.type_expr option
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  let rec translate_decomposed loc type_desc =
    match T.get type_desc with
    | UnionNotInitialized -> Error.union_no_init_err "type"
    | Builtin b -> transl_builtin_type loc b
    | Pointer p -> transl_pointer_type loc p
    | Record r -> transl_record_type loc r
    | EnumType e -> transl_enum_type loc e
    | Elaborated e -> transl_elaborated_type e
    | Typedef t -> transl_typedef_type loc t
    | FixedWidth f -> transl_fixed_width_type loc f
    | LValueRef l -> transl_lvalue_ref_type loc l
    | RValueRef l -> transl_rvalue_ref_type loc l
    | SubstTemplateTypeParam s -> transl_subst_template_type_param loc s
    | Undefined _ -> failwith "Undefined type."
    | _ -> Error.error loc "Unsupported type."

  and translate type_node =
    Node_translator.map ~f:translate_decomposed type_node

  and translate_return_type (type_node : R.Node.t) : Ast.type_expr option =
    match translate type_node with
    | Ast.ManifestTypeExpr (_, Ast.Void) -> None
    | rt -> Some rt

  and transl_builtin_type (loc : Ast.loc) (bt : T.BuiltinKind.t) : Ast.type_expr
      =
    let make_man t = Ast.ManifestTypeExpr (loc, t) in
    let open T.BuiltinKind in
    let make_int signed rank = make_man @@ Ast.Int (signed, rank) in
    match bt with
    | Char -> make_int Ast.Signed @@ Ast.CharRank
    | UChar -> make_int Ast.Unsigned @@ Ast.CharRank
    | Short -> make_int Ast.Signed @@ Ast.ShortRank
    | UShort -> make_int Ast.Unsigned @@ Ast.ShortRank
    | Void -> make_man Ast.Void
    | Bool -> make_man Ast.Bool
    | Int -> make_int Ast.Signed IntRank
    | UInt -> make_int Ast.Unsigned IntRank
    | Long -> make_int Ast.Signed LongRank
    | ULong -> make_int Ast.Unsigned LongRank
    | LongLong -> make_int Ast.Signed @@ LongLongRank
    | ULongLong -> make_int Ast.Unsigned @@ LongLongRank
    | _ -> Error.error loc "Unsupported builtin type."

  and transl_pointer_type (loc : Ast.loc) (ptr : R.Node.t) : Ast.type_expr =
    let pointee_type = translate ptr in
    Ast.PtrTypeExpr (loc, pointee_type)

  and transl_lvalue_ref_type (loc : Ast.loc) (l : R.Node.t) : Ast.type_expr =
    let ref_type = translate l in
    Ast.LValueRefTypeExpr (loc, ref_type)

  and transl_rvalue_ref_type (loc : Ast.loc) (l : R.Node.t) : Ast.type_expr =
    let ref_type = translate l in
    Ast.RValueRefTypeExpr (loc, ref_type)

  and transl_elaborated_type (e : R.Node.t) : Ast.type_expr = translate e

  and transl_typedef_type (loc : Ast.loc) (id : string) : Ast.type_expr =
    Ast.IdentTypeExpr (loc, None, id)

  and transl_record_type (loc : Ast.loc) (r : R.RecordRef.t) : Ast.type_expr =
    let open R.RecordRef in
    let name = name_get r in
    match kind_get r with
    | R.RecordKind.(Struc | Class) ->
        Ast.StructTypeExpr (loc, Some name, None, [], [])
    | R.RecordKind.Unio -> Ast.UnionTypeExpr (loc, Some name, None)

  and transl_enum_type (loc : Ast.loc) (name : string) : Ast.type_expr =
    Ast.EnumTypeExpr (loc, Some name, None)

  and transl_fixed_width_type (loc : Ast.loc) (fw : T.FixedWidth.t) :
      Ast.type_expr =
    let open T.FixedWidth in
    let rank =
      match bits_get fw with
      | 8 -> Ast.FixedWidthRank 0
      | 16 -> Ast.FixedWidthRank 1
      | 32 -> Ast.FixedWidthRank 2
      | 64 -> Ast.FixedWidthRank 3
      | 128 -> Ast.FixedWidthRank 4
      | n ->
          Error.error loc @@ "Invalid fixed width specified in type: "
          ^ string_of_int n
    in
    let signed =
      match kind_get fw with
      | FixedWidthKind.Int -> Ast.Signed
      | FixedWidthKind.UInt -> Ast.Unsigned
    in
    ManifestTypeExpr (loc, Ast.Int (signed, rank))

  and transl_subst_template_type_param (loc : Ast.loc) (st : R.Node.t) :
      Ast.type_expr =
    translate st
end
