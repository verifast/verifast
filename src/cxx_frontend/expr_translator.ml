module R = Reader.R
module E = R.Expr

module type Translator = sig
  val translate : R.Node.t -> Ast.expr
  val make_int_lit : Ast.loc -> int -> Ast.expr
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  module Type_translator = Type_translator.Make (Node_translator)

  let make_int_lit (loc : Ast.loc) (n : int) =
    Ast.IntLit (loc, Big_int.big_int_of_int n, true, false, Ast.NoLSuffix)

  let rec translate_decomposed loc expr_desc =
    match E.get expr_desc with
    | UnionNotInitialized -> Error.union_no_init_err "expression"
    | UnaryOp op -> transl_unary_op_expr loc op
    | BinaryOp op -> transl_binary_op_expr loc op
    | IntLit int_lit -> transl_int_lit_expr loc int_lit
    | BoolLit bool_lit -> transl_bool_lit_expr loc bool_lit
    | StringLit str_lit -> transl_str_lit_expr loc str_lit
    | Call c -> transl_call_expr loc c
    | DeclRef ref -> transl_decl_ref_expr loc ref
    | This -> transl_this_expr loc
    | New n -> transl_new_expr loc n
    | Construct c -> transl_construct_expr loc c
    | Member m -> transl_member_expr loc m
    | MemberCall c -> transl_member_call_expr loc c
    | NullPtrLit -> transl_null_ptr_lit_expr loc
    | Delete d -> transl_delete_expr loc d
    | Truncating t -> transl_trunc_expr loc t
    | LValueToRValue l -> transl_lvalue_to_rvalue_expr loc l
    | DerivedToBase e -> transl_derived_to_base_expr loc e
    | OperatorCall o -> transl_operator_call_expr loc o
    | Cleanups c -> transl_cleanups_expr c
    | BindTemporary t -> transl_bind_temporary_expr t
    | IntegralCast c -> transl_integral_cast loc c
    | ConditionalOp op -> transl_conditional_op loc op
    | Undefined _ -> failwith "Undefined expression"
    | _ -> Error.error loc "Unsupported expression."

  and translate expr_node =
    Node_translator.map ~f:translate_decomposed expr_node

  and transl_unary_op_expr (loc : Ast.loc) (op : E.UnaryOp.t) : Ast.expr =
    let open E.UnaryOp in
    let operand = translate @@ operand_get op in
    let make_assign loc op lhs post =
      Ast.AssignOpExpr (loc, lhs, op, make_int_lit loc 1, post)
    in
    match kind_get op with
    | R.UnaryOpKind.Plus -> operand (* +i *)
    | R.UnaryOpKind.Minus ->
        Ast.Operation (loc, Ast.Sub, [ make_int_lit loc 0; operand ]) (* -i *)
    | R.UnaryOpKind.Not -> Ast.Operation (loc, Ast.BitNot, [ operand ]) (* ~ *)
    | R.UnaryOpKind.LNot -> Ast.Operation (loc, Ast.Not, [ operand ]) (* ! *)
    | R.UnaryOpKind.AddrOf -> Ast.AddressOf (loc, operand) (* &i *)
    | R.UnaryOpKind.Deref -> Ast.Deref (loc, operand) (* *i *)
    | R.UnaryOpKind.PreInc -> make_assign loc Ast.Add operand false (* --i *)
    | R.UnaryOpKind.PreDec -> make_assign loc Ast.Sub operand false (* ++i *)
    | R.UnaryOpKind.PostInc -> make_assign loc Ast.Add operand true (* i++ *)
    | R.UnaryOpKind.PostDec -> make_assign loc Ast.Sub operand true (* i-- *)
    | _ -> Error.error loc "Unsupported unary expression."

  and transl_binary_op_expr (loc : Ast.loc) (op : E.BinaryOp.t) : Ast.expr =
    let open E.BinaryOp in
    let lhs = translate @@ lhs_get op in
    let rhs = translate @@ rhs_get op in
    let make_op loc op lhs rhs = Ast.Operation (loc, op, [ lhs; rhs ]) in
    let make_assign loc op lhs rhs =
      Ast.AssignOpExpr (loc, lhs, op, rhs, false)
    in
    match kind_get op with
    (* binary operators *)
    | R.BinaryOpKind.Add -> make_op loc Ast.Add lhs rhs (* + *)
    | R.BinaryOpKind.Sub -> make_op loc Ast.Sub lhs rhs (* - *)
    | R.BinaryOpKind.Mul -> make_op loc Ast.Mul lhs rhs (* * *)
    | R.BinaryOpKind.Div -> make_op loc Ast.Div lhs rhs (* / *)
    | R.BinaryOpKind.Rem -> make_op loc Ast.Mod lhs rhs (* % *)
    | R.BinaryOpKind.Shl -> make_op loc Ast.ShiftLeft lhs rhs (* << *)
    | R.BinaryOpKind.Shr -> make_op loc Ast.ShiftRight lhs rhs (* >> *)
    | R.BinaryOpKind.Lt -> make_op loc Ast.Lt lhs rhs (* < *)
    | R.BinaryOpKind.Gt -> make_op loc Ast.Gt lhs rhs (* > *)
    | R.BinaryOpKind.Le -> make_op loc Ast.Le lhs rhs (* <= *)
    | R.BinaryOpKind.Ge -> make_op loc Ast.Ge lhs rhs (* >= *)
    | R.BinaryOpKind.Eq -> make_op loc Ast.Eq lhs rhs (* == *)
    | R.BinaryOpKind.Ne -> make_op loc Ast.Neq lhs rhs (* != *)
    | R.BinaryOpKind.Or -> make_op loc Ast.BitOr lhs rhs (* | *)
    | R.BinaryOpKind.And -> make_op loc Ast.BitAnd lhs rhs (* & *)
    | R.BinaryOpKind.Xor -> make_op loc Ast.BitXor lhs rhs (* ^ *)
    | R.BinaryOpKind.LAnd -> make_op loc Ast.And lhs rhs (* && *)
    | R.BinaryOpKind.LOr -> make_op loc Ast.Or lhs rhs (* || *)
    (* regular assign *)
    | R.BinaryOpKind.Assign -> Ast.AssignExpr (loc, lhs, rhs) (* = *)
    (* assign operator *)
    | R.BinaryOpKind.MulAssign -> make_assign loc Ast.Mul lhs rhs (* *= *)
    | R.BinaryOpKind.DivAssign -> make_assign loc Ast.Div lhs rhs (* /= *)
    | R.BinaryOpKind.RemAssign -> make_assign loc Ast.Mod lhs rhs (* %= *)
    | R.BinaryOpKind.AddAssign -> make_assign loc Ast.Add lhs rhs (* += *)
    | R.BinaryOpKind.SubAssign -> make_assign loc Ast.Sub lhs rhs (* -= *)
    | R.BinaryOpKind.ShlAssign ->
        make_assign loc Ast.ShiftLeft lhs rhs (* <<= *)
    | R.BinaryOpKind.ShrAssign ->
        make_assign loc Ast.ShiftRight lhs rhs (* >>= *)
    | R.BinaryOpKind.AndAssign -> make_assign loc Ast.BitAnd lhs rhs (* &= *)
    | R.BinaryOpKind.XorAssign -> make_assign loc Ast.BitXor lhs rhs (* ^= *)
    | R.BinaryOpKind.OrAssign -> make_assign loc Ast.BitOr lhs rhs (* |= *)
    | _ -> Error.error loc "Unsupported binary expression."

  and transl_int_lit_expr (loc : Ast.loc) (int_lit : E.IntLit.t) : Ast.expr =
    let open Stdint in
    let open Big_int in
    let big_int_of_uint64 (value : Stdint.uint64) =
      let lowPart = Uint64.to_int64 (Uint64.logand value (Uint64.of_int 0xFFFFFFFF)) in
      let highPart = Uint64.to_int64 (Uint64.shift_right value 32) in
      let result = ref (big_int_of_int64 highPart) in
      result := shift_left_big_int !result 32;
      or_big_int (big_int_of_int64 lowPart) !result
    in

    let open E.IntLit in
    let l_suf =
      match l_suffix_get int_lit with
      | R.SufKind.LSuf -> Ast.LSuffix
      | R.SufKind.LLSuf -> Ast.LLSuffix
      | R.SufKind.NoSuf -> Ast.NoLSuffix
    in
    let dec =
      match base_get int_lit with
      | R.NbBase.Decimal -> true
      | _ -> false
    in
    let u_suf = u_suffix_get int_lit in
    let low_bits = big_int_of_uint64 (low_bits_get int_lit) in
    let high_bits = big_int_of_uint64 (high_bits_get int_lit) in
    let value = or_big_int (shift_left_big_int high_bits 64) low_bits in
    Ast.IntLit (loc, value, dec, u_suf, l_suf)

  and transl_bool_lit_expr (loc : Ast.loc) (bool_lit : bool) : Ast.expr =
    match bool_lit with true -> Ast.True loc | false -> Ast.False loc

  and transl_str_lit_expr (loc : Ast.loc) (str_lit : string) : Ast.expr =
    Ast.StringLit (loc, str_lit)

  and map_args (args : R.Node.t Capnp_util.capnp_arr) : Ast.pat list =
    args |> Capnp_util.arr_map (fun e -> Ast.LitPat (translate e))

  and transl_call (loc : Ast.loc) (call : E.Call.t) : string * Ast.pat list =
    let open E.Call in
    let callee = callee_get call in
    let args = args_get call |> map_args in
    let name =
      let callee_loc, desc = Node_translator.decompose callee in
      let e = E.get desc in
      match e with
      | E.DeclRef r ->
          (* c-like function call, operator calls (even tho they can be class methods) *)
          r
      | E.Member m ->
          (* C++ method call on explicit or implicit (this) object *)
          E.Member.name_get m
      | _ -> Error.error loc "Unsupported callee in function or method call."
    in
    (name, args)

  and transl_call_expr (loc : Ast.loc) (call : E.Call.t) : Ast.expr =
    let name, args = transl_call loc call in
    Ast.CallExpr (loc, name, [], [], args, Ast.Static)

  and transl_operator_call_expr (loc : Ast.loc) (call : E.Call.t) : Ast.expr =
    let name, Ast.LitPat this_arg :: args = transl_call loc call in
    let args =
      Ast.LitPat (Ast.make_addr_of (Ast.expr_loc this_arg) this_arg) :: args
    in
    Ast.CallExpr (loc, name, [], [], args, Ast.Static)

  and transl_member_call_expr (loc : Ast.loc) (member_call : E.MemberCall.t) :
      Ast.expr =
    let open E.MemberCall in
    let name, args = call_get member_call |> transl_call loc in
    let impl_arg =
      let arg = implicit_arg_get member_call |> translate in
      if arrow_get member_call then arg
      else Ast.make_addr_of (Ast.expr_loc arg) arg
    in
    let args = Ast.LitPat impl_arg :: args in
    let binding =
      if target_has_qualifier_get member_call then Ast.Static else Ast.Instance
    in
    Ast.CallExpr (loc, name, [], [], args, binding)

  and transl_decl_ref_expr (loc : Ast.loc) (ref : string) : Ast.expr =
    Ast.Var (loc, ref)

  and transl_this_expr (loc : Ast.loc) : Ast.expr = Ast.Var (loc, "this")

  and transl_construct_expr (loc : Ast.loc) (c : E.Construct.t) : Ast.expr =
    let open E.Construct in
    let name = name_get c in
    let ty = type_get c |> Type_translator.translate_decomposed loc in
    let args = args_get c |> Capnp_util.arr_map translate in
    Ast.CxxConstruct (loc, name, ty, args)

  and transl_new_expr (loc : Ast.loc) (n : E.New.t) : Ast.expr =
    let open E.New in
    let expr_opt =
      if has_expr n then Some (expr_get n |> translate) else None
    in
    let ty = type_get n |> Type_translator.translate_decomposed loc in
    Ast.CxxNew (loc, ty, expr_opt)

  and transl_delete_expr (loc : Ast.loc) (d : R.Node.t) : Ast.expr =
    let e = translate d in
    Ast.CxxDelete (loc, e)

  and transl_member_expr (loc : Ast.loc) (m : E.Member.t) : Ast.expr =
    let open E.Member in
    let base = translate @@ base_get m in
    let field = name_get m in
    let arrow = arrow_get m in
    (* let qual_name = qual_name_get m in *)
    (* could be useful in the future *)
    if arrow then Ast.Read (loc, base, field) else Ast.Select (loc, base, field)

  and transl_null_ptr_lit_expr (loc : Ast.loc) = make_int_lit loc 0

  and transl_trunc_expr (loc : Ast.loc) (t : R.Node.t) : Ast.expr =
    let e = translate t in
    Ast.TruncatingExpr (loc, e)

  and transl_lvalue_to_rvalue_expr (loc : Ast.loc) (e : R.Node.t) : Ast.expr =
    let e = translate e in
    Ast.CxxLValueToRValue (loc, e)

  and transl_derived_to_base_expr (loc : Ast.loc) (e : E.Cast.t) :
      Ast.expr =
    let open E.Cast in
    let sub_expr = expr_get e |> translate in
    let ty = type_get e |> Type_translator.translate_decomposed loc in
    Ast.CxxDerivedToBase (loc, sub_expr, ty)

  and transl_integral_cast (loc : Ast.loc) (c : E.Cast.t) : Ast.expr =
    let open E.Cast in
    let sub_expr = expr_get c |> translate in
    let ty = type_get c |> Type_translator.translate_decomposed loc in
    Ast.CastExpr (loc, ty, sub_expr)

  and transl_conditional_op (loc : Ast.loc) (op : E.ConditionalOp.t) : Ast.expr =
    let open E.ConditionalOp in
    let cond = translate @@ cond_get op in
    let th = translate @@ then_get op in
    let el = translate @@ else_get op in
    Ast.IfExpr(loc, cond, th, el)

  and transl_cleanups_expr (e : R.Node.t) : Ast.expr = translate e
  and transl_bind_temporary_expr (e : R.Node.t) = translate e
end
