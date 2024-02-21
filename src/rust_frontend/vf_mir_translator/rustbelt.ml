open Ast

type tid = expr
type v = expr
type lft = expr
type l = expr
type vid = string (* value id *)

type ty_interp = {
  size : expr;
  own : tid -> v list -> (asn, string) result;
  own_predname : (string, string) result;
  shr : lft -> tid -> l -> (asn, string) result;
  full_bor_content : (string, string) result;
  points_to : tid -> l -> vid option -> (asn, string) result;
}

let emp_ty_interp loc =
  {
    size = True loc;
    own = (fun _ _ -> Ok (True loc));
    own_predname = Error "Not yet supported";
    shr = (fun _ _ _ -> Ok (True loc));
    full_bor_content = Error "Not yet supported";
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
