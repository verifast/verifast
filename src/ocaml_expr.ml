open Ast
open Big_int
open Num

type ocaml_expr =
  C of string * ocaml_expr list (* variant constructor *)
| S of string (* string *)
| I of int (* int *)
| B of bool (* bool *)
| BigInt of big_int
| Num of num
| L of ocaml_expr list (* list *)
| T of ocaml_expr list (* tuple *)
| Ref of < id: Obj.t; contents: ocaml_expr >
| Call of string * ocaml_expr list
| Loc of loc

let of_ref f r =
  Ref
    object
      method id = Obj.repr r
      method contents = f !r
    end

let c ctor = C (ctor, [])
let s x = S x
let i x = I x
let b x = B x
