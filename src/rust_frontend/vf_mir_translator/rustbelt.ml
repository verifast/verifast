open Ast

type tid = expr
type v = expr
type lft = expr
type l = expr
type vid = string (* value id *)

type ty_interp = {
  size : expr;
  own : tid -> v -> (asn, string) result;
  own_pred : (Ast.expr, string) result;
  shr : lft -> tid -> l -> (asn, string) result; (* Should be duplicable, e.g. a dummy pattern. The caller will not wrap this in a dummy coef asn. *)
  shr_pred : (Ast.expr, string) result; (* Need not be duplicable; the caller will wrap this in a dummy pattern. *)
  full_bor_content : tid -> l -> (Ast.expr, string) result;
  points_to : tid -> l -> vid option -> (asn, string) result;
}

let simple_fbc loc fbc_name tid l = Ok (CallExpr (loc, fbc_name, [], [], [LitPat tid; LitPat l], Static))

let emp_ty_interp loc =
  {
    size = True loc;
    own = (fun _ _ -> Ok (True loc));
    own_pred = Error "Not yet supported";
    shr = (fun _ _ _ -> Error "Not yet supported");
    shr_pred = Error "Not yet supported";
    full_bor_content = (fun _ _ -> Error "Not yet supported");
    points_to = (fun _ _ _ -> Ok (True loc));
  }

module Aux = struct
  open Ast

  let vid_op_to_var_pat vid_op loc =
    match vid_op with
    | None -> Ok DummyVarPat
    | Some vid when vid != "" -> Ok (VarPat (loc, vid))
    | _ -> Error "empty value id string"

  (* Todo @Nima: write a function to generate points_to for all types and use it in translate_T_ty functions *)
end
