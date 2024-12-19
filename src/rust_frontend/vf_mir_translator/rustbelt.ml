open Ast

type tid = expr
type v = expr
type lft = expr
type l = expr
type vid = string (* value id *)

type ty_interp = {
  size : expr;
  own : tid -> v -> (asn, string) result;
  shr : lft -> tid -> l -> (asn, string) result; (* Should be duplicable, e.g. a dummy pattern. The caller will not wrap this in a dummy coef asn. *)
  full_bor_content : tid -> l -> (Ast.expr, string) result;
  points_to : tid -> l -> vid option -> (asn, string) result;
  pointee_fbc : (tid -> string (* l *) -> string (* suffix for bound variables *) -> (asn, string) result) option; (* None if this type is not a reference type *)
}

let simple_fbc loc fbc_name tid l = Ok (CallExpr (loc, fbc_name, [], [], [LitPat tid; LitPat l], Static))

module Aux = struct
  open Ast

  let vid_op_to_var_pat vid_op loc =
    match vid_op with
    | None -> Ok DummyVarPat
    | Some vid when vid != "" -> Ok (VarPat (loc, vid))
    | _ -> Error "empty value id string"

  (* Todo @Nima: write a function to generate points_to for all types and use it in translate_T_ty functions *)
end

let emp_ty_interp loc =
  {
    size = True loc;
    own = (fun _ _ -> Ok (True loc));
    shr = (fun _ _ _ -> Error "Not yet supported");
    full_bor_content = (fun _ _ -> Error "Not yet supported");
    points_to = (fun t l v ->
      Result.bind (Aux.vid_op_to_var_pat v loc) @@ fun pat ->
      Ok (PointsTo (loc, l, RegularPointsTo, pat)));
    pointee_fbc = None;
  }
