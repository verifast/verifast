(*

Copyright (C) 2013 Katholieke Universiteit Leuven
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the <organization> nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

open Misc
open General_ast

module Ast_writer = struct

(* ------------------------ *)
(* Auxilary print functions *)
(* ------------------------ *)

let indentation = ref ""
let indent () = indentation:= !indentation ^ " "
let unindent () = indentation:= String.sub !indentation 0 (String.length !indentation - 1)
let new_line () = Printf.printf "%s" "\n"
let print s = Printf.printf "%s" s
let print_indent s = Printf.printf "%s%s" !indentation s
let print_line s = 
  print_indent s;
  new_line ()

let print_wrapped begin_ middle end_ =
  print_line begin_;
  indent();
  middle ();
  unindent();
  new_line ();
  print_indent end_
  
let print_constructor name args =
  match args with
    []    -> print_indent name;
  | _     -> 
      let middle () =
        let nb_of_args = List.length args in
        let print_arg i arg =
          arg ();
          if i < nb_of_args - 1 then print ",\n"
        in
        iteri print_arg args;  
      in
      print_wrapped (name ^ "(") middle ")"

let string_limit = 50
let shorten_string s =
  let shorten =
    if String.length s <= string_limit then
      s
    else
      (String.sub s 0 string_limit) ^ " ... "
  in
  shorten

(* mics *)
let string_of_string s =
  "\"" ^ (shorten_string s) ^ "\""
let parenthesize l =
  "(" ^ (String.concat ", " l) ^ ")"
let string_of_srcpos ((p, f), l, c) =
  parenthesize [
     parenthesize [string_of_string p; string_of_string f]; 
     string_of_int l; 
     string_of_int c
  ]

(* ------------------------ *)
(* AST writing functions    *)
(* ------------------------ *)
  
(* main write function *)
let rec write_ast package =
  write_package package ();
  print_line ""
  

(* basic write functions *)
and write_string s () =
  print_indent (string_of_string s)
and write_boolean b () =
  match b with
    true -> print_indent "true"
  | false -> print_indent "false"
and write_list l () =
  match l with
    [] -> print_indent "[]"
  | _  -> 
      let middle () =
        let nb_of_elems = List.length l in
        let print_elem i e =
          e ();
          if i < nb_of_elems - 1 then print ";\n"
        in
        iteri print_elem l;  
      in
      print_wrapped "[" middle "]"
and write_option : 'a . ('a -> unit -> unit) -> ('a option) -> unit -> unit =
  fun f arg _ ->
    match arg with 
      Some x -> 
        print_line "Some(";
        indent ();
        f x ();
        unindent ();
        new_line ();
        print_indent ")"
    | None -> print_indent "None"


(* locations *)
and write_location (l1, l2) () =
  print_indent (parenthesize [string_of_srcpos l1; string_of_srcpos l2])


(* annotations *)
and write_annotation a () =
  match a with Annotation(l, value) ->
    let args = 
      [write_location l;
       write_string value]
    in
    print_constructor "Annotation" args;


(* Accessibility *)
and write_accessibility access () =
  match access with 
    PublicAccess -> print_constructor "PublicAccess" []
  | PackageAccess -> print_constructor "PackageAccess" []
  | PrivateAccess -> print_constructor "PrivateAccess" []


(* names *)
and write_id id () =
  match id with Identifier(l, id) ->
    let args = 
      [write_location l;
       write_string id]
    in
    print_constructor "Identifier" args;
and write_name name () =
  match name with Name(l, ids) ->
    let args = 
      [write_location l;
       write_list (List.map write_id ids)]
    in
    print_constructor "Name" args;


(* types *)
and write_type t () =
  match t with
    PrimType(t) ->
      let args = 
        [write_prim_type t]
      in
      print_constructor "PrimType" args;
  | RefType(t) ->
      let args = 
        [write_ref_type t]
      in
      print_constructor "RefType" args;
  | ArrayType(t) ->
      let args = 
        [write_ref_type t]
      in
      print_constructor "ArrayType" args;
and write_prim_type t () =
  match t with
  | VoidType   l -> print_constructor "VoidType" [write_location l];
  | BoolType   l -> print_constructor "BoolType" [write_location l];
  | CharType   l -> print_constructor "CharType" [write_location l];
  | ByteType   l -> print_constructor "ByteType" [write_location l];
  | ShortType  l -> print_constructor "ShortType" [write_location l];
  | IntType    l -> print_constructor "IntType" [write_location l];
  | LongType   l -> print_constructor "LongType" [write_location l];
  | FloatType  l -> print_constructor "FLoatType" [write_location l];
  | DoubleType l -> print_constructor "DoubleType" [write_location l];
and write_ref_type t () =
  match t with 
    SimpleRef(name) ->
      let args = 
        [write_name name]
      in
      print_constructor "SimpleRef" args;
  | TypeApply(l, name, types) ->
      let args = 
        [write_location l;
         write_name name;
         write_list (List.map write_ref_type types)]
      in
      print_constructor "TypeApply" args;
  | WildCard(l, typ, bound) ->
      let args = 
        [write_location l;
         write_option write_ref_type typ;
         write_bound_kind bound]
      in
      print_constructor "WildCard" args;
and write_bound_kind k () =
  match k with 
    Upper -> print_constructor "Upper" []
  | Lower -> print_constructor "Lower" []
and write_type_param p () =
  match p with TypeParam(l, id, types) ->
    let args = 
      [write_location l;
       write_id id;
       write_list (List.map write_ref_type types)]
    in
    print_constructor "TypeParam" args;


(* package level *)
and write_package p () =
  match p with Package(l, name, imports, decls) ->
    let args = 
      [write_location l;
       write_name name;
       write_list (List.map write_import imports);
       write_list (List.map write_package_decl decls)]
    in
    print_constructor "Package" args;
and write_import i () =
  match i with Import(l, name, id) ->
    let args = 
      [write_location l;
       write_name name;
       write_option write_id id]
    in
    print_constructor "Import" args;
and write_package_decl decl () =
  match decl with
    P_Annotation a ->
      let args = 
        [write_annotation a]
      in
      print_constructor "P_Annotation" args;
  | P_Class c ->
      let args = 
        [write_class c]
      in
      print_constructor "P_Class" args;
and write_class c () =
  match c with 
    Class (l, anns, id, tparams, access, abs, final, stat, extends, impls, decls) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_id id;
         write_list (List.map write_type_param tparams);
         write_accessibility access;
         write_boolean abs;
         write_boolean final;
         write_boolean stat;
         write_option write_ref_type extends;
         write_list (List.map write_ref_type impls);
         write_list (List.map write_class_decl decls)]
      in
      print_constructor "Class" args;
  | Interface (l, anns, id, tparams, access, extends, decls) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_id id;
         write_list (List.map write_type_param tparams);
         write_accessibility access;
         write_list (List.map write_ref_type extends);
         write_list (List.map write_class_decl decls)]
      in
      print_constructor "Interface" args;
  | Enum (l, anns, id, access, ids) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_id id;
         write_accessibility access;
         write_list (List.map write_id ids)]
      in
      print_constructor "Enum" args;
    

(* class level *)
and write_class_decl decl () =
  match decl with 
    C_Variable v ->
      let args = 
        [write_var_decl v]
      in
      print_constructor "C_Variable" args;
  | C_Method m ->
      let args = 
        [write_meth_decl m]
      in
      print_constructor "C_Method" args;
  | C_Annotation a -> 
      let args = 
        [write_annotation a]
      in
      print_constructor "C_Annotation" args;
  | C_Class c -> 
      let args = 
        [write_class c]
      in
      print_constructor "C_Class" args;
and write_var_decl var () =
  match var with Variable (l, id, access, prot, final, stat, typ, expr) ->
    let args = 
      [write_location l;
        write_id id;
        write_accessibility access;
        write_boolean prot;
        write_boolean final;
        write_boolean stat;
        write_type typ;
        write_option write_expression expr]
    in
    print_constructor "Variable" args;
and write_meth_decl meth () =
  match meth with 
    Constructor (l, anns, id, tparams, access, prot, params, exceps, stmts, auto) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_id id;
         write_list (List.map write_type_param tparams);
         write_accessibility access;
         write_boolean prot;
         write_list (List.map write_var_decl params);
         write_list (List.map write_exception exceps);
         write_list (List.map write_statement stmts);
         write_boolean auto]
      in
      print_constructor "Constructor" args;
  | Method (l, anns, id, tparams, access, prot, abs, final, stat, ret, params, exceps, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_id id;
         write_list (List.map write_type_param tparams);
         write_accessibility access;
         write_boolean prot;
         write_boolean abs;
         write_boolean final;
         write_boolean stat;
         write_type ret;
         write_list (List.map write_var_decl params);
         write_list (List.map write_exception exceps);
         write_option (fun x -> write_list (List.map write_statement x)) stmts]
      in
      print_constructor "Method" args;
and write_exception (typ, ann) () =
  let middle () =
    write_ref_type typ ();
    print_line ",";
    write_annotation ann ()
  in
  print_wrapped "(" middle ")"


(* statements *)
and write_statement stmt () =
  match stmt with
  | S_Annotation(a) -> 
      let args = 
        [write_annotation a]
      in
      print_constructor "S_Annotation" args;
  | S_Variable(v) ->
      let args = 
        [write_var_decl v]
      in
      print_constructor "S_Variable" args;
  | S_Expression(e) ->
      let args = 
        [write_expression e]
      in
      print_constructor "S_Expression" args;
  | Block(l, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_statement stmts);]
      in
      print_constructor "Block" args;
  | Try(l, stmts, catchers) ->
      let args = 
        [write_location l;
         write_list (List.map write_statement stmts);
         write_list (List.map write_catcher catchers)]
      in
      print_constructor "Try" args;
  | DoWhile(l, anns, e, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_expression e;
         write_list (List.map write_statement stmts)]
      in
      print_constructor "DoWhile" args;
  | While(l, anns, e, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_expression e;
         write_list (List.map write_statement stmts)]
      in
      print_constructor "While" args;
  | For(l, anns, inits, cond, updates, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_list (List.map write_statement inits);
         write_expression cond;
         write_list (List.map write_statement updates);
         write_list (List.map write_statement stmts)]
      in
      print_constructor "For" args;
  | Foreach(l, anns, var, cont, stmts) ->
      let args = 
        [write_location l;
         write_list (List.map write_annotation anns);
         write_var_decl var;
         write_expression cont;
         write_list (List.map write_statement stmts)]
      in
      print_constructor "Foreach" args;
  | Labeled(l, id, stmt) ->
      let args = 
        [write_location l;
         write_id id;
         write_statement stmt]
      in
      print_constructor "Labeled" args;    
  | Switch(l, sel, cases, default) ->
      let args = 
        [write_location l;
         write_expression sel;
         write_list (List.map write_case cases);
         write_option write_case default]
      in
      print_constructor "Switch" args;   
  | If(l, e, stmt_if, stmt_else) ->
     let args = 
        [write_location l;
         write_expression e;
         write_statement stmt_if;
         write_statement stmt_else]
      in
      print_constructor "If" args;
  | Break(l) ->
     let args = 
        [write_location l]
      in
      print_constructor "Break" args;
  | Continue(l) ->
     let args = 
        [write_location l]
      in
      print_constructor "Continue" args;
  | Return(l, e) ->
     let args = 
        [write_location l;
         write_expression e]
      in
      print_constructor "Return" args;
  | Throw(l, e) ->
     let args = 
        [write_location l;
         write_expression e]
      in
      print_constructor "Throw" args;
  | Assert(l, e1, e2) ->
     let args = 
        [write_location l;
         write_expression e1;
         write_expression e2]
      in
      print_constructor "Assert" args;
and write_case case () =
  match case with Case (l, matched, stmts) ->
    let args = 
      [write_location l;
       write_option write_expression matched;
       write_list (List.map write_statement stmts)]
    in
    print_constructor "Case" args;
and write_catcher catch () =
  match catch with Catch (l, var, stmts) ->
    let args = 
      [write_location l;
       write_var_decl var;
        write_list (List.map write_statement stmts)]
    in
    print_constructor "Catch" args;

(* expressions *)
and write_expression e () =
  match e with
  | E_Identifier(id) ->
      let args = 
        [write_id id]
      in
      print_constructor "E_Identifier" args;
  | Access(l, e, id) ->
      let args = 
        [write_location l;
         write_expression e;
         write_id id]
      in
      print_constructor "Access" args;
  | Apply(l, tparams, meth, args) ->
      let args = 
        [write_location l;
         write_list (List.map write_type_param tparams);
         write_expression meth;
         write_list (List.map write_expression args)]
      in
      print_constructor "Apply" args;
  | NewClass(l, tparams, typ, args) ->
      let args = 
        [write_location l;
         write_list (List.map write_type_param tparams);
         write_ref_type typ;
         write_list (List.map write_expression args)]
      in
      print_constructor "NewClass" args;
  | NewArray(l, typ, inits) ->
      let args = 
        [write_location l;
         write_type typ;
         write_list (List.map write_expression inits)]
      in
      print_constructor "NewArray" args;
  | Assign(l, binop, el, er) ->
      let args = 
        [write_location l;
         write_option write_bin_operator binop;
         write_expression el;
         write_expression er]
      in
      print_constructor "Assign" args;
  | Unary(l, unop, e) ->
      let args = 
        [write_location l;
         write_uni_operator unop;
         write_expression e]
      in
      print_constructor "Unary" args;
  | Binary(l, binop, el, er) ->
      let args = 
        [write_location l;
         write_bin_operator binop;
         write_expression el;
         write_expression er]
      in
      print_constructor "Binary" args;
  | Ternary(l, cond, et, ef) ->
      let args = 
        [write_location l;
         write_expression cond;
         write_expression et;
         write_expression ef]
      in
      print_constructor "Ternary" args;
  | TypeCast(l, typ, e) ->
      let args = 
        [write_location l;
         write_type typ;
         write_expression e]
      in
      print_constructor "TypeCast" args;
  | ArrayAccess(l, array_, index) ->
      let args = 
        [write_location l;
         write_expression array_;
         write_expression index]
      in
      print_constructor "ArrayAccess" args;
  | Literal(l, typ, value) ->
      let args = 
        [write_location l;
         write_type typ;
         write_string value]
      in
      print_constructor "Literal" args;

(* operators *)
and write_bin_operator o () =
  match o with
  | O_Plus   -> print_constructor "O_Plus" []
  | O_Min    -> print_constructor "O_Min" []
  | O_Mul    -> print_constructor "O_Mul" []
  | O_Div    -> print_constructor "O_Div" []
  | O_Mod    -> print_constructor "O_Mod" []
  | O_Or     -> print_constructor "O_Or" []
  | O_And    -> print_constructor "O_And" []
  | O_Eq     -> print_constructor "O_Eq" []
  | O_NotEq  -> print_constructor "O_NotEq" []
  | O_Lt     -> print_constructor "O_Lt" []
  | O_Gt     -> print_constructor "O_Gt" []
  | O_LtEq   -> print_constructor "O_LtEq" []
  | O_GtEq   -> print_constructor "O_GtEq" []
  | O_BitOr  -> print_constructor "O_BitOr" []
  | O_BitXor -> print_constructor "O_BitXor" []
  | O_BitAnd -> print_constructor "O_BitAnd" []
  | O_ShiftL  -> print_constructor "O_ShiftL" []
  | O_ShiftR  -> print_constructor "O_ShiftR" []
  | O_UShiftR -> print_constructor "O_UShiftR" []
and write_uni_operator o () =
  match o with
  | O_Pos     -> print_constructor "O_Pos" []
  | O_Neg     -> print_constructor "O_Neg" []
  | O_Not     -> print_constructor "O_Not" []
  | O_Compl   -> print_constructor "O_Compl" []
  | O_PreInc  -> print_constructor "O_PreInc" []
  | O_PreDec  -> print_constructor "O_PreDec" []
  | O_PostInc -> print_constructor "O_PostInc" []
  | O_PostDec -> print_constructor "O_PostDec" []

  
end
(* -------------------------- *)
(* End                        *)
(* -------------------------- *)

