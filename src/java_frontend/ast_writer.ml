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

(* ------------------------ *)
(* Auxilary print functions *)
(* ------------------------ *)

let indentation = ref ""
let indent () = indentation:= !indentation ^ "  "
let unindent () = indentation:= String.sub !indentation 0 (String.length !indentation - 2)

let print_line s = Printf.printf "%s%s\n" !indentation s
let print_line_node header value print_loc loc = 
  let loc = if print_loc then ("(" ^ (string_of_loc loc) ^ ")") else "" in
  print_line (header ^ ":\"" ^ value ^ "\"" ^ loc ^ ";")
let print_block_node header value print_loc loc = 
  let loc = if print_loc then ("(" ^ (string_of_loc loc) ^ ")") else "" in
  print_line (header ^ ":\"" ^ value ^ "\"" ^ loc ^ ";"); 
  print_line "{"; 
  indent()
let print_block_node_end () = 
  unindent(); 
  print_line "}"
let print_wrapped header func l = 
  print_block_node "Wrapped" header false dummy_loc;
  List.iter func l;
  print_block_node_end ()

(* ------------------------ *)
(* AST writing functions    *)
(* ------------------------ *)

(* main write function *)
let rec write_ast package =
  write_package package


(* verifier annotations *)
and write_annotation ann =
  match ann with
    Annotation(l, value) ->
      print_block_node "Annotation" "" true l;
      Printf.printf "\"%s\"\n" value;
      print_block_node_end ()


(* types *)
and write_prim_type t =
  let l = 
    match t with
    | VoidType(l)  -> l
    | BoolType(l)  -> l
    | CharType(l)  -> l
    | ByteType(l)  -> l
    | ShortType(l) -> l
    | IntType(l)   -> l
    | LongType(l)  -> l
    | FloatType(l) -> l
    | DoubleType(l)-> l
  in
  print_line_node "BasicType" (string_of_prim_type t) true l
and write_ref_type t =
  let l = 
    match t with
    | SimpleRef(Name(l, _)) -> l
    | TypeApply(l, _, _) -> l
    | WildCard(l, _, _) -> l
  in
  print_line_node "RefType" (string_of_ref_type t) true l
and write_type t =
  match t with 
    PrimType t -> write_prim_type t
  | RefType t -> write_ref_type t
  | ArrayType t -> write_ref_type t
and write_type_param tparam = 
  match tparam with
    TypeParam(l, id, bounds) ->
      print_block_node "TypeParam" (string_of_identifier id) true l;
      List.iter write_ref_type bounds;
      print_block_node_end ()


(* package level *)
and write_package package =
  match package with
    Package(l, name, imprts, decls) ->
      begin
        print_block_node "Package" (string_of_name name) true l;
        List.iter write_import imprts;
        List.iter write_package_decl decls;
        print_block_node_end ()
      end
and write_import import =
  match import with
    Import(l, package, item) ->
      let name = 
        match item with
          Some(Identifier(_, x)) -> x
        | None -> "*"
      in
      print_line_node "Import" (((string_of_name package)) ^ "." ^ name) true l 
and write_package_decl decl =
  match decl with
    P_Annotation(a) ->
      write_annotation a
  | P_Class(c) ->
      write_class c


(* class level *)
and write_class c =
  match c with
  | Class(l, anns, ident, tparams, access, fin, abs, stat, extnds, inters, decls) ->
      let header = 
        "Class [" ^ (string_of_accessibility access) ^
        (if abs  then " abstract" else "") ^
        (if fin  then " final" else "") ^
        (if stat then " static" else "") ^ "]"
      in
      print_block_node header (string_of_identifier ident) true l;
      List.iter write_annotation anns;
      print_wrapped "TypeParams" write_type_param tparams;
      (match extnds with
        Some x -> 
          print_block_node "Extends" "" false dummy_loc;
          write_ref_type x;
          print_block_node_end ()
      | None -> ());
      print_wrapped "Implements" write_ref_type inters;
      List.iter write_class_decl decls;
      print_block_node_end ()
  | Interface(l, anns, ident, tparams, access, inters, decls) ->
      print_block_node ("Interface [" ^ (string_of_accessibility access) ^ "]") (string_of_identifier ident) true l;
      List.iter write_annotation anns;
      print_wrapped "TypeParams" write_type_param tparams;
      print_wrapped "Extends" write_ref_type inters;
      List.iter write_class_decl decls;
      print_block_node_end ()
  | Enum(l, anns, ident, access, values) ->
      print_block_node ("Enum [" ^ (string_of_accessibility access) ^ "]") 
                       (string_of_identifier ident) true l;
      List.iter write_annotation anns;
      List.iter (fun x -> print_line (string_of_identifier x)) values;
      print_block_node_end ()
and write_class_decl decl =
  match decl with
    C_Method(m) ->
        write_meth_decl m
  | C_Variable(v) ->
        write_var_decl v
  | C_Annotation(a) ->
      write_annotation a
  | C_Class(c) ->
      write_class c
and write_meth_decl meth =
  match meth with
    Constructor(l, anns, id, tparams, access, prot, params, thrown, _, _) ->
      print_block_node ("Constructor [" ^ 
        (if prot then " protected" else (string_of_accessibility access)) ^ 
        "]") (string_of_identifier id) true l;
      List.iter write_annotation anns;
      print_wrapped "TypeParams" write_type_param tparams;
      List.iter write_var_decl params;
      print_wrapped "Thrown" (fun (excep, ann) -> write_ref_type excep; write_annotation ann) thrown;
(*       write_block block; *)
      print_block_node_end ()
  | Method(l, anns, id, tparams, access, prot, abs, fin, stat, ret, params, thrown, _) ->
      let header = 
        "Method [" ^
        (if prot then " protected" else (string_of_accessibility access)) ^
        (if abs  then " abstract" else "") ^
        (if fin  then " final" else "") ^
        (if stat then " static" else "") ^ "]"
      in
      print_block_node header (string_of_identifier id) true l;
      List.iter write_annotation anns;
      print_wrapped "TypeParams" write_type_param tparams;
      write_type ret;
      List.iter write_var_decl params;
      print_wrapped "Thrown" (fun (excep, ann) -> write_ref_type excep; write_annotation ann) thrown;
(*       write_block block; *)
      print_block_node_end ()
and write_var_decl var =
  match var with
    Variable(l, id, access, prot, fin, stat, typ, _) ->
      let header = 
        "Variable [" ^ 
        (if prot then " protected" else (string_of_accessibility access)) ^
        (if fin  then " final" else "") ^
        (if stat then " static" else "") ^ "]"
      in
      print_block_node header (string_of_identifier id) true l;
      write_type typ;
(*      match init with
          Some e -> write_expression e
        | _ -> ();*)
      print_block_node_end ()

(* ************************************************************************************** *)
(* TODO!!!!!! *************************************************************************** *)
(* ************************************************************************************** *)
(* ************************************************************************************** *)

(* statements *)

(* expressions *)

(* ************************************************************************************** *)
(* ************************************************************************************** *)
(* ************************************************************************************** *)
(* ************************************************************************************** *)
end


(* -------------------------- *)
(* End                        *)
(* -------------------------- *)

