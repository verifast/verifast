open Ast
open Verifast0

let rec string_of_type_expr = function
  ManifestTypeExpr (l, tp) -> rust_string_of_type tp
| IdentTypeExpr (l, None, x) -> x
| StructTypeExpr (l, Some sn, None, [], targs) -> Printf.sprintf "%s%s" sn (string_of_type_targs targs)
| ConstructedTypeExpr (l, tn, targs) -> Printf.sprintf "%s%s" tn (string_of_type_targs targs)
| RustRefTypeExpr (l, lft, mut, tp) -> Printf.sprintf "&%s%s %s" (string_of_type_expr lft) (match mut with Mutable -> " mut" | Shared -> "") (string_of_type_expr tp)
| PtrTypeExpr (l, tp) -> Printf.sprintf "*%s" (string_of_type_expr tp)
| SliceTypeExpr (l, tp) -> Printf.sprintf "[%s]" (string_of_type_expr tp)
| te -> failwith (Printf.sprintf "string_of_type_expr: %s" (Ocaml_expr_formatter.string_of_ocaml_expr true (Ocaml_expr_of_ast.of_type_expr te)))
and string_of_type_targs = function
  [] -> ""
| ts -> Printf.sprintf "<%s>" (String.concat ", " (List.map string_of_type_expr ts))

let string_of_val_targs = function
  [] -> ""
| ts -> Printf.sprintf "::<%s>" (String.concat ", " (List.map string_of_type_expr ts))

let string_of_tparam (x, bounds) = x

let string_of_tparams = function
  [] -> ""
| tps -> "<" ^ String.concat ", " (List.map string_of_tparam tps) ^ ">"

let string_of_params ps =
  String.concat ", " (List.map (fun (tp, x) -> Printf.sprintf "%s: %s" x (string_of_type_expr tp)) ps)

let string_of_ret = function
  None -> ""
| Some tp -> " -> " ^ string_of_type_expr tp

let rec string_of_expr = function
  Var (l, x) -> x
| CallExpr (l, "lft_of", [], [], [LitPat (Typeid (_, TypeExpr (IdentTypeExpr (_, None, x))))], Static) when String.starts_with ~prefix:"'" x -> x
| CallExpr (l, f, targs, ps1, ps2, binding) ->
  let args1 = if ps1 = [] then "" else Printf.sprintf "(%s)" (string_of_pats ps1) in
  Printf.sprintf "%s%s%s(%s)" f (string_of_val_targs targs) args1 (string_of_pats ps2)
| TypePredExpr (l, te, p) -> Printf.sprintf "<%s>.%s" (string_of_type_expr te) p
| Typeid (l, e) -> Printf.sprintf "typeid(%s)" (string_of_expr e)
| TypeExpr te -> string_of_type_expr te
| Select (l, e, f) -> Printf.sprintf "%s.%s" (string_of_expr e) f
| Operation (l, Eq, [e1; e2]) -> Printf.sprintf "%s == %s" (string_of_expr e1) (string_of_expr e2)
| True l -> "true"
| CastExpr (l, StructTypeExpr (_, Some sn, _, [], targs), InitializerList (_, fs)) ->
  Printf.sprintf "%s%s { %s }" sn (string_of_val_targs targs) (String.concat ", " (List.map (fun (Some (_, f), e) -> Printf.sprintf "%s: %s" f (string_of_expr e)) fs))
| CastExpr (l, te, e) -> Printf.sprintf "%s as %s" (string_of_expr e) (string_of_type_expr te)
| e -> failwith (Printf.sprintf "string_of_expr: %s" (Ocaml_expr_formatter.string_of_ocaml_expr true (Ocaml_expr_of_ast.of_expr e)))
and string_of_pats ps = String.concat ", " (List.map string_of_pat ps)
and string_of_pat = function
    VarPat (l, x) -> Printf.sprintf "?%s" x
  | LitPat e -> string_of_expr e
  | DummyPat -> "_"

let rec string_of_bool_expr = function
  CallExpr (l, f, targs, ps1, ps2, binding) ->
  let args1 = if ps1 = [] then "" else Printf.sprintf "(%s)" (string_of_pats ps1) in
  Printf.sprintf "%s%s%s(%s) == true" f (string_of_val_targs targs) args1 (string_of_pats ps2)
| e -> string_of_expr e

let rec string_of_asn = function
  CallExpr (l, f, targs, ps1, ps2, binding) ->
  let args1 = if ps1 = [] then "" else Printf.sprintf "(%s)" (string_of_pats ps1) in
  Printf.sprintf "%s%s%s(%s)" f (string_of_val_targs targs) args1 (string_of_pats ps2)
| ExprCallExpr (l, epred, eargs) -> Printf.sprintf "%s(%s)" (string_of_expr epred) (string_of_pats eargs)
| Sep (l, e1, e2) -> Printf.sprintf "%s &*& %s" (string_of_asn e1) (string_of_asn e2)
| ExprAsn (l, e) -> string_of_bool_expr e
| CoefAsn (l, coef_pat, e) -> Printf.sprintf "[%s]%s" (string_of_pat coef_pat) (string_of_asn e)
| EmpAsn l -> "emp"
| e -> string_of_bool_expr e

let string_of_decl (d: decl) =
  match d with
  | Func (l, Lemma (false, None), tparams, rt, f, ps, nonghost_callers_only, (None, None), Some (pre, (result_var, post)), false, None, false, []) ->
    Printf.sprintf "lem %s%s(%s)%s\n    req %s;\n    ens %s;\n{\n    assume(false);\n}" f (string_of_tparams tparams) (string_of_params ps) (string_of_ret rt) (string_of_asn pre) (string_of_asn post)
