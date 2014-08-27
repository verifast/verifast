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

open General_ast

module Ast_writer = struct

(* ----------------------------- *)
(* Auxilary string_for functions *)
(* ----------------------------- *)

let indentation = ref ""
let indent () = indentation:= !indentation ^ "  "
let unindent () = indentation:= String.sub !indentation 0 (String.length !indentation - 2)
let new_line () = "\n"
let string_limit = 50
let shorten_string s =
  let shorten =
    if String.length s <= string_limit then
      s
    else
      (String.sub s 0 string_limit) ^ " ... "
  in
  shorten
let shorten_string s = s
let string_for_indent s = Printf.sprintf "%s%s" !indentation s
let string_line s = 
  (string_for_indent s) ^
  (new_line ())
let quoted_string s =
  "\"" ^ (shorten_string s) ^ "\""
let parenthesize l =
  "(" ^ (String.concat ", " l) ^ ")"

let string_wrapped begin_ middle end_ =
  let s1 = string_line begin_ in
  indent ();
  let s2 = middle () in
  unindent();
  let s3 = (new_line ()) ^ (string_for_indent end_) in
  s1 ^ s2 ^ s3
  
let string_for_constructor name args =
  match args with
    []    -> string_for_indent name;
  | _     -> 
      let middle () =
        String.concat ",\n" (List.map (fun x -> x ()) args);
      in
      string_wrapped (name ^ "(") middle ")"

let string_for_string s () =
  string_for_indent (quoted_string s)
let string_for_int i () =
  string_of_int i
let string_for_boolean b () =
  match b with
    true -> string_for_indent "true"
  | false -> string_for_indent "false"
let string_for_list l () =
  match l with
    [] -> string_for_indent "[]"
  | _  -> 
      let middle () =
        String.concat ";\n" (List.map (fun x -> x ()) l);
      in
      string_wrapped "[" middle "]"
let string_for_option : ('a -> unit -> string) -> ('a option) -> unit -> string =
  fun f arg _ ->
    match arg with 
      Some x -> 
        let s1 = string_line "Some(" in
        indent ();
        let s2 = f x () in
        unindent ();
        let s3 = (new_line ()) ^ (string_for_indent ")") in
        s1 ^ s2 ^ s3
    | None -> string_for_indent "None"


(* ------------------------ *)
(* Main function            *)
(* ------------------------ *)
  
(* main write function *)
let rec write_ast package =
  print_string ((string_for_package package ()) ^ "\n");

(* ------------------------ *)
(* AST string_for functions *)
(* ------------------------ *)

(* locations *)
and string_for_location loc () =
  let l =
    match loc with
      NoSource -> "NoSource"
    | SourceLine(p, l, c1, c2) -> 
        "SourceLine(" ^ (quoted_string p) ^ ", "
                      ^ (string_of_int l) ^ ", "
                      ^ (string_of_int c1) ^ ", "
                      ^ (string_of_int c2) ^ ")"
    | SourceLines(p, l1, c1, l2, c2) -> 
        "SourceLines(" ^ (quoted_string p) ^ ", "
                      ^ (string_of_int l1) ^ ", "
                      ^ (string_of_int c1) ^ ", "
                      ^ (string_of_int l2) ^ ", "
                      ^ (string_of_int c2) ^ ")"
  in
  string_for_indent l
and string_for_gen_source source () =
  match source with
  | Original -> string_for_constructor "Original" []
  | Generated -> string_for_constructor "Generated" []


(* annotations *)
and string_for_annotation a () =
  match a with Annotation(l, value) ->
    let s = string_for_indent "Annotation(\n" in
    indent ();
    let s = s ^ (string_for_location l ()) ^ ",\n" in
    unindent ();
    s ^ (quoted_string value) ^ "\n" ^ string_for_indent ")"

(* Accessibility *)
and string_for_accessibility access () =
  match access with 
  | PublicAccess -> string_for_constructor "PublicAccess" []
  | PackageAccess -> string_for_constructor "PackageAccess" []
  | ProtectedAccess -> string_for_constructor "ProtectedAccess" []
  | PrivateAccess -> string_for_constructor "PrivateAccess" []
and string_for_static_binding binding () =
  match binding with 
  | Static -> string_for_constructor "Static" []
  | NonStatic -> string_for_constructor "NonStatic" []
and string_for_abstractness abs () =
  match abs with 
  | Abstract -> string_for_constructor "Abstract" []
  | NonAbstract -> string_for_constructor "NonAbstract" [] 
and string_for_finality final () =
  match final with 
  | Final -> string_for_constructor "Final" []
  | NonFinal -> string_for_constructor "NonFinal" []


(* names *)
and string_for_id id () =
  match id with Identifier(l, id) ->
    let args = 
      [string_for_location l;
       string_for_string id]
    in
    string_for_constructor "Identifier" args;
and string_for_name name () =
  match name with Name(l, ids) ->
    let args = 
      [string_for_location l;
       string_for_list (List.map string_for_id ids)]
    in
    string_for_constructor "Name" args;


(* types *)
and string_for_type t () =
  match t with
    PrimType(t) ->
      let args = 
        [string_for_prim_type t]
      in
      string_for_constructor "PrimType" args;
  | RefType(t) ->
      let args = 
        [string_for_ref_type t]
      in
      string_for_constructor "RefType" args;
  | ArrayType(t) ->
      let args = 
        [string_for_type t]
      in
      string_for_constructor "ArrayType" args;
and string_for_prim_type t () =
  match t with
  | VoidType   l -> string_for_constructor "VoidType" [string_for_location l];
  | BoolType   l -> string_for_constructor "BoolType" [string_for_location l];
  | CharType   l -> string_for_constructor "CharType" [string_for_location l];
  | ByteType   l -> string_for_constructor "ByteType" [string_for_location l];
  | ShortType  l -> string_for_constructor "ShortType" [string_for_location l];
  | IntType    l -> string_for_constructor "IntType" [string_for_location l];
  | LongType   l -> string_for_constructor "LongType" [string_for_location l];
  | FloatType  l -> string_for_constructor "FloatType" [string_for_location l];
  | DoubleType l -> string_for_constructor "DoubleType" [string_for_location l];
and string_for_ref_type t () =
  match t with 
    SimpleRef(name) ->
      let args = 
        [string_for_name name]
      in
      string_for_constructor "SimpleRef" args;
  | TypeApply(l, name, types) ->
      let args = 
        [string_for_location l;
         string_for_name name;
         string_for_list (List.map string_for_ref_type types)]
      in
      string_for_constructor "TypeApply" args;
  | WildCard(l, typ, bound) ->
      let args = 
        [string_for_location l;
         string_for_option string_for_ref_type typ;
         string_for_bound_kind bound]
      in
      string_for_constructor "WildCard" args;
and string_for_bound_kind k () =
  match k with 
  | Upper   -> string_for_constructor "Upper" []
  | Lower   -> string_for_constructor "Lower" []
  | Unbound -> string_for_constructor "Unbound" []
and string_for_type_param p () =
  match p with TypeParam(l, id, types) ->
    let args = 
      [string_for_location l;
       string_for_id id;
       string_for_list (List.map string_for_ref_type types)]
    in
    string_for_constructor "TypeParam" args;


(* package level *)
and string_for_package p () =
  match p with Package(l, name, imports, decls) ->
    let args = 
      [string_for_location l;
       string_for_name name;
       string_for_list (List.map string_for_import imports);
       string_for_list (List.map string_for_package_decl decls)]
    in
    string_for_constructor "Package" args;
and string_for_import i () =
  match i with Import(l, name, id) ->
    let args = 
      [string_for_location l;
       string_for_name name;
       string_for_option string_for_id id]
    in
    string_for_constructor "Import" args;
and string_for_package_decl decl () =
  match decl with
    P_Annotation a ->
      let args = 
        [string_for_annotation a]
      in
      string_for_constructor "P_Annotation" args;
  | P_Class c ->
      let args = 
        [string_for_class c]
      in
      string_for_constructor "P_Class" args;
and string_for_class c () =
  match c with 
  | Class (l, anns, id, tparams, access, abs, final, stat, extends, impls, decls) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_id id;
         string_for_list (List.map string_for_type_param tparams);
         string_for_accessibility access;
         string_for_abstractness abs;
         string_for_finality final;
         string_for_static_binding stat;
         string_for_option string_for_ref_type extends;
         string_for_list (List.map string_for_ref_type impls);
         string_for_list (List.map string_for_class_decl decls)]
      in
      string_for_constructor "Class" args;
  | Interface (l, anns, id, tparams, access, extends, decls) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_id id;
         string_for_list (List.map string_for_type_param tparams);
         string_for_accessibility access;
         string_for_list (List.map string_for_ref_type extends);
         string_for_list (List.map string_for_class_decl decls)]
      in
      string_for_constructor "Interface" args;
  | Enum (l, anns, id, access, ids) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_id id;
         string_for_accessibility access;
         string_for_list (List.map string_for_id ids)]
      in
      string_for_constructor "Enum" args;
    

(* class level *)
and string_for_class_decl decl () =
  match decl with 
  | C_Annotation a -> 
      let args = 
        [string_for_annotation a]
      in
      string_for_constructor "C_Annotation" args;
  | C_Class c -> 
      let args = 
        [string_for_class c]
      in
      string_for_constructor "C_Class" args;
  | StaticBlock(l, stmts) -> 
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_statement stmts)]
      in
      string_for_constructor "StaticBlock" args;
  | Field(l, id, access, final, stat, typ, e, auto) ->
      let args = 
        [string_for_location l;
         string_for_id id;
         string_for_accessibility access;
         string_for_finality final;
         string_for_static_binding stat;
         string_for_type typ;
         string_for_option string_for_expression e;
         string_for_gen_source auto]
      in
      string_for_constructor "Field" args;
  | Constructor (l, anns, tparams, access, params, exceps, stmts, auto) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_list (List.map string_for_type_param tparams);
         string_for_accessibility access;
         string_for_list (List.map string_for_var_decl params);
         string_for_list (List.map string_for_exception exceps);
         string_for_option (fun x -> string_for_list (List.map string_for_statement x)) stmts;
         string_for_gen_source auto]
      in
      string_for_constructor "Constructor" args;
  | Method (l, anns, id, tparams, access, abs, final, stat, ret, params, exceps, stmts, auto) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_id id;
         string_for_list (List.map string_for_type_param tparams);
         string_for_accessibility access;
         string_for_abstractness abs;
         string_for_finality final;
         string_for_static_binding stat;
         string_for_type ret;
         string_for_list (List.map string_for_var_decl params);
         string_for_list (List.map string_for_exception exceps);
         string_for_option (fun x -> string_for_list (List.map string_for_statement x)) stmts;
         string_for_gen_source auto]
      in
      string_for_constructor "Method" args;
and string_for_var_decl var () =
  match var with Variable (l, id, typ, expr) ->
    let args = 
      [string_for_location l;
        string_for_id id;
        string_for_type typ;
        string_for_option string_for_expression expr]
    in
    string_for_constructor "Variable" args;
and string_for_exception (typ, ann) () =
  let middle () =
    (string_for_ref_type typ ()) ^ (",\n") ^
    (string_for_option (fun x -> string_for_annotation x) ann) ()
  in
  string_wrapped "(" middle ")"


(* statements *)
and string_for_statement stmt () =
  match stmt with
  | S_Annotation(a) -> 
      let args = 
        [string_for_annotation a]
      in
      string_for_constructor "S_Annotation" args;
  | S_Variable(v) ->
      let args = 
        [string_for_var_decl v]
      in
      string_for_constructor "S_Variable" args;
  | S_Expression(e) ->
      let args = 
        [string_for_expression e]
      in
      string_for_constructor "S_Expression" args;
  | Block(l, stmts) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_statement stmts);]
      in
      string_for_constructor "Block" args;
  | Try(l, stmts, catchers) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_statement stmts);
         string_for_list (List.map write_catcher catchers)]
      in
      string_for_constructor "Try" args;
  | DoWhile(l, anns, e, stmts) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_expression e;
         string_for_list (List.map string_for_statement stmts)]
      in
      string_for_constructor "DoWhile" args;
  | While(l, anns, e, stmts) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_expression e;
         string_for_list (List.map string_for_statement stmts)]
      in
      string_for_constructor "While" args;
  | For(l, anns, inits, cond, updates, stmts) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_list (List.map string_for_statement inits);
         string_for_expression cond;
         string_for_list (List.map string_for_statement updates);
         string_for_list (List.map string_for_statement stmts)]
      in
      string_for_constructor "For" args;
  | Foreach(l, anns, var, cont, stmts) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_annotation anns);
         string_for_var_decl var;
         string_for_expression cont;
         string_for_list (List.map string_for_statement stmts)]
      in
      string_for_constructor "Foreach" args;
  | Labeled(l, id, stmt) ->
      let args = 
        [string_for_location l;
         string_for_id id;
         string_for_statement stmt]
      in
      string_for_constructor "Labeled" args;    
  | Switch(l, sel, cases, default) ->
      let args = 
        [string_for_location l;
         string_for_expression sel;
         string_for_list (List.map string_for_case cases);
         string_for_option string_for_case default]
      in
      string_for_constructor "Switch" args;   
  | If(l, e, stmts_if, stmts_else) ->
     let args = 
        [string_for_location l;
         string_for_expression e;
         string_for_list (List.map string_for_statement stmts_if);
         string_for_list (List.map string_for_statement stmts_else)]
      in
      string_for_constructor "If" args;
  | Break(l) ->
     let args = 
        [string_for_location l]
      in
      string_for_constructor "Break" args;
  | Continue(l) ->
     let args = 
        [string_for_location l]
      in
      string_for_constructor "Continue" args;
  | Return(l, e) ->
     let args = 
        [string_for_location l;
         string_for_option string_for_expression e]
      in
      string_for_constructor "Return" args;
  | Throw(l, e) ->
     let args = 
        [string_for_location l;
         string_for_expression e]
      in
      string_for_constructor "Throw" args;
  | Assert(l, e1, e2) ->
     let args = 
        [string_for_location l;
         string_for_expression e1;
         string_for_option string_for_expression e2]
      in
      string_for_constructor "Assert" args;
and string_for_case case () =
  match case with Case (l, matched, stmts) ->
    let args = 
      [string_for_location l;
       string_for_option string_for_expression matched;
       string_for_list (List.map string_for_statement stmts)]
    in
    string_for_constructor "Case" args;
and write_catcher catch () =
  match catch with Catch (l, var, stmts) ->
    let args = 
      [string_for_location l;
       string_for_var_decl var;
       string_for_list (List.map string_for_statement stmts)]
    in
    string_for_constructor "Catch" args;


(* expressions *)
and string_for_expression e () =
  match e with
  | E_Identifier(id) ->
      let args = 
        [string_for_id id;]
      in
      string_for_constructor "E_Identifier" args;
  | Access(l, e, id) ->
      let args = 
        [string_for_location l;
         string_for_expression e;
         string_for_id id;]
      in
      string_for_constructor "Access" args;
  | Apply(l, tparams, e, arg_types, args) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_type_param tparams);
         string_for_expression e;
         string_for_list (List.map string_for_type arg_types);
         string_for_list (List.map string_for_expression args);]
      in
      string_for_constructor "Apply" args;
  | NewClass(l, tparams, clss, args) ->
      let args = 
        [string_for_location l;
         string_for_list (List.map string_for_type_param tparams);
         string_for_ref_type clss;
         string_for_list (List.map string_for_expression args);]
      in
      string_for_constructor "NewClass" args;
  | NewArray(l, typ, dims, inits) ->
      let args = 
        [string_for_location l;
         string_for_type typ;
         string_for_list (List.map string_for_expression dims);
         string_for_list (List.map string_for_expression inits)]
      in
      string_for_constructor "NewArray" args;
  | Assign(l, binop, el, er) ->
      let args = 
        [string_for_location l;
         string_for_option string_for_bin_operator binop;
         string_for_expression el;
         string_for_expression er]
      in
      string_for_constructor "Assign" args;
  | Unary(l, unop, e) ->
      let args = 
        [string_for_location l;
         string_for_uni_operator unop;
         string_for_expression e]
      in
      string_for_constructor "Unary" args;
  | Binary(l, binop, el, er) ->
      let args = 
        [string_for_location l;
         string_for_bin_operator binop;
         string_for_expression el;
         string_for_expression er]
      in
      string_for_constructor "Binary" args;
  | Ternary(l, cond, et, ef) ->
      let args = 
        [string_for_location l;
         string_for_expression cond;
         string_for_expression et;
         string_for_expression ef]
      in
      string_for_constructor "Ternary" args;
  | TypeCast(l, typ, e) ->
      let args = 
        [string_for_location l;
         string_for_type typ;
         string_for_expression e]
      in
      string_for_constructor "TypeCast" args;
  | TypeTest(l, typ, e) ->
      let args = 
        [string_for_location l;
         string_for_type typ;
         string_for_expression e]
      in
      string_for_constructor "TypeTest" args;
  | ArrayAccess(l, array_, index) ->
      let args = 
        [string_for_location l;
         string_for_expression array_;
         string_for_expression index]
      in
      string_for_constructor "ArrayAccess" args;
  | Literal(l, typ, value) ->
      let args = 
        [string_for_location l;
         string_for_type typ;
         string_for_string value]
      in
      string_for_constructor "Literal" args;

(* operators *)
and string_for_bin_operator o () =
  match o with
  | O_Plus   -> string_for_constructor "O_Plus" []
  | O_Min    -> string_for_constructor "O_Min" []
  | O_Mul    -> string_for_constructor "O_Mul" []
  | O_Div    -> string_for_constructor "O_Div" []
  | O_Mod    -> string_for_constructor "O_Mod" []
  | O_Or     -> string_for_constructor "O_Or" []
  | O_And    -> string_for_constructor "O_And" []
  | O_Eq     -> string_for_constructor "O_Eq" []
  | O_NotEq  -> string_for_constructor "O_NotEq" []
  | O_Lt     -> string_for_constructor "O_Lt" []
  | O_Gt     -> string_for_constructor "O_Gt" []
  | O_LtEq   -> string_for_constructor "O_LtEq" []
  | O_GtEq   -> string_for_constructor "O_GtEq" []
  | O_BitOr  -> string_for_constructor "O_BitOr" []
  | O_BitXor -> string_for_constructor "O_BitXor" []
  | O_BitAnd -> string_for_constructor "O_BitAnd" []
  | O_ShiftL  -> string_for_constructor "O_ShiftL" []
  | O_ShiftR  -> string_for_constructor "O_ShiftR" []
  | O_UShiftR -> string_for_constructor "O_UShiftR" []
and string_for_uni_operator o () =
  match o with
  | O_Pos     -> string_for_constructor "O_Pos" []
  | O_Neg     -> string_for_constructor "O_Neg" []
  | O_Not     -> string_for_constructor "O_Not" []
  | O_Compl   -> string_for_constructor "O_Compl" []
  | O_PreInc  -> string_for_constructor "O_PreInc" []
  | O_PreDec  -> string_for_constructor "O_PreDec" []
  | O_PostInc -> string_for_constructor "O_PostInc" []
  | O_PostDec -> string_for_constructor "O_PostDec" []

  
end
(* -------------------------- *)
(* End                        *)
(* -------------------------- *)
