open Rocq_writer
open Ast

let rec of_type t =
  match unfold_inferred_type t with
  | PtrType t -> App ("RawPtr", [of_type t])
  | Int (Signed, FixedWidthRank k) ->
    let size =
      match k with
        0 -> "U8"
      | 1 -> "U16"
      | 2 -> "U32"
      | 3 -> "U64"
      | 4 -> "U128"
    in
    App ("Int", [Ident size])
  | Int (Signed, PtrRank) ->
    App ("Int", [Ident "Isize"])
  | Int (Unsigned, FixedWidthRank k) ->
    let size =
      match k with
        0 -> "U8"
      | 1 -> "U16"
      | 2 -> "U32"
      | 3 -> "U64"
      | 4 -> "U128"
    in
    App ("Uint", [Ident size])
  | Int (Unsigned, PtrRank) ->
    App ("Uint", [Ident "Usize"])
  | _ -> Ident "UnknownType"

let rec of_expr = function
| True l -> Ident "True"
| WVar (l, x, LocalVar) -> App ("Var", [StringLiteral x])
| WPureFunCall (l, "null_pointer", [], []) -> Ident "NullPtr"
| WOperation (l, Eq, [e1; e2], _) -> App ("Eq", [of_expr e1; of_expr e2])
| Upcast (e, t1, t2) -> of_expr e
| CastExpr (l, _, e) -> of_expr e
| RealLit (l, n, None) -> App ("RealLit", [RealLiteral n])
| _ -> Ident "UnknownExpr"

let of_pat = function
| LitPat e -> App ("LitPat", [of_expr e])
| VarPat (l, x) -> App ("VarPat", [StringLiteral x])
| DummyPat -> Ident "DummyPat"

let rec of_asn = function
| WPointsTo (l, WDeref (_, lhs, _), tp, _, rhs) ->
  App ("PointsToAsn", [of_type tp; of_expr lhs; of_pat rhs])
| WPredAsn (l, g, true, [], [], pats) ->
  begin match g#name with
  | PredFam g ->
    App ("PredAsn", [StringLiteral g; List (List.map of_pat pats)])
  end
| ExprAsn (l, e) -> App ("BoolAsn", [of_expr e])
| Sep (l, asn1, asn2) ->
  App ("SepAsn", [of_asn asn1; of_asn asn2])
| IfAsn (l, cond, asn_then, asn_else) ->
  App ("IfAsn", [of_expr cond; of_asn asn_then; of_asn asn_else])
| _ -> Ident "UnknownAsn"