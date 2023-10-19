open Ast
open Big_int
open Num
open Format

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

let rec pp_print_ocaml_expr f = function
  C (ctor, []) ->
  pp_print_string f ctor
| C (ctor, args) ->
  pp_open_box f 2;
  pp_print_string f ctor;
  pp_print_space f ();
  pp_print_string f "(";
  pp_print_list ~pp_sep:(fun f () -> pp_print_string f ","; pp_print_space f ()) pp_print_ocaml_expr f args;
  pp_print_string f ")";
  pp_close_box f ()
| S s -> fprintf f "%S" s
| I i -> fprintf f "%d" i
| B b -> fprintf f "%B" b
| BigInt n -> fprintf f "big_int_of_string@ %S" (string_of_big_int n)
| Num n -> fprintf f "num_of_string@ %S" (string_of_num n)
| L es ->
  pp_print_string f "[";
  pp_open_hvbox f 2;
  pp_print_cut f ();
  pp_print_list ~pp_sep:(fun f () -> pp_print_string f ";"; pp_print_space f ()) pp_print_ocaml_expr f es;
  pp_print_cut f ();
  pp_close_box f ();
  pp_print_string f "]"
| T es ->
  pp_print_string f "(";
  pp_open_box f 2;
  pp_print_list ~pp_sep:(fun f () -> pp_print_string f ","; pp_print_space f ()) pp_print_ocaml_expr f es;
  pp_close_box f ();
  pp_print_string f ")"
| Ref r ->
  (* TODO: create the same ref only once *)
  pp_print_string f "ref";
  pp_print_space f ();
  pp_print_string f "(";
  pp_open_box f 2;
  pp_print_ocaml_expr f r#contents;
  pp_close_box f ();
  pp_print_string f ")"
| Call (fn, []) ->
  pp_print_string f fn
| Call (fn, args) ->
  pp_print_string f fn;
  pp_print_space f ();
  pp_print_list ~pp_sep:pp_print_space pp_print_ocaml_expr f args
| Loc l ->
  pp_print_string f "loc";
  pp_print_space f ();
  fprintf f "%S" (string_of_loc l)

let fprint_ocaml_expr_newline chan e =
  let f = formatter_of_out_channel chan in
  pp_print_ocaml_expr f e;
  pp_print_newline f ()

let emit path e =
  let chan = open_out path in
  fprint_ocaml_expr_newline chan e;
  close_out chan
