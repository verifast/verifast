open Big_int
open Num
open Ocaml_expr

type tree =
  Atom of string
| Break
| Trees of tree list
| List of tree list

let rec tree_contains_nonempty_list = function
  List [] -> false
| List _ -> true
| Trees ts -> List.exists tree_contains_nonempty_list ts
| _ -> false

let print_tree print_string t =
  let rec print_tree indent = function
    Atom s -> print_string s
  | Break -> print_string " "
  | Trees ts -> List.iter (print_tree indent) ts
  | List ts ->
    if List.exists tree_contains_nonempty_list ts then begin
      let newIndent = indent ^ "  " in
      List.iter begin fun t ->
        print_string "\n";
        print_string newIndent;
        print_tree newIndent t
      end ts;
      print_string "\n";
      print_string indent
    end else begin
      let t::ts = ts in
      print_tree indent t;
      List.iter begin fun t ->
        print_string " ";
        print_tree indent t
      end ts
    end
  in
  print_tree "" t

let tree_of_ocaml_expr noLocs e =
  let rec tree_of_ocaml_expr = function
    C (ctor, []) ->
    Atom ctor
    | C (ctor, [arg]) ->
    Trees [Atom ctor; Break; Atom "("; tree_of_ocaml_expr arg; Atom ")"]
    | C (ctor, arg::args) ->
    let argsTrees = List.fold_right begin fun e ts ->
        Atom ","::Break::tree_of_ocaml_expr e::ts
    end args [Atom ")"] in
    Trees (Atom ctor::Break::Atom "("::tree_of_ocaml_expr arg::argsTrees)
    | S s -> Atom (Printf.sprintf "%S" s)
    | I i -> Atom (Printf.sprintf "%d" i)
    | B b -> Atom (Printf.sprintf "%B" b)
    | BigInt n -> Trees [Atom "big_int_of_string"; Break; Atom (Printf.sprintf "%S" (string_of_big_int n))]
    | Num n -> Trees [Atom "num_of_string"; Break; Atom (Printf.sprintf "%S" (string_of_num n))]
    | L [] -> Atom "[]"
    | L es ->
    let rec trees_of_exprs es =
        match es with
        [e] -> [tree_of_ocaml_expr e]
        | e::es -> Trees [tree_of_ocaml_expr e; Atom ";"]::trees_of_exprs es
    in
    Trees [Atom "["; List (trees_of_exprs es); Atom "]"]
    | T [] -> Atom "()"
    | T [e] -> Trees [Atom "("; tree_of_ocaml_expr e; Atom ")"]
    | T (e::es) ->
    let esTrees = List.fold_right begin fun e ts ->
        Atom ","::Break::tree_of_ocaml_expr e::ts
    end es [Atom ")"] in
    Trees (Atom "("::tree_of_ocaml_expr e::esTrees)
    | Ref r ->
    Trees [Atom "ref"; Break; Atom "("; tree_of_ocaml_expr r#contents; Atom ")"]
    | Call (f, args) ->
    let argsTrees = List.fold_right begin fun e ts ->
        Break::tree_of_ocaml_expr e::ts
    end args [] in
    Trees (Atom f::argsTrees)
    | Loc l ->
    if noLocs then Atom "l" else Trees [Atom "loc"; Break; Atom (Printf.sprintf "%S" (Ast.string_of_loc l))]
  in
  tree_of_ocaml_expr e

let print_ocaml_expr_to_file noLocs path e =
  let chan = open_out path in
  print_tree (output_string chan) (tree_of_ocaml_expr noLocs e);
  close_out chan

let string_of_ocaml_expr noLocs e =
  let buf = Buffer.create 10 in
  print_tree (Buffer.add_string buf) (tree_of_ocaml_expr noLocs e);
  Buffer.contents buf
