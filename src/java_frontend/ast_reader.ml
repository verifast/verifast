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

open Stream
open Big_int

open Misc
open General_ast

module Ast_reader = struct

exception AstReaderException of loc * string
let error l s = raise (AstReaderException(l, s))
(* debug print *)
let debug_print x = 
  Printf.printf "<OCaml debug> ast_reader.ml - %s\n" x
let debug_print x = ()

(* ------------------------ *)
(* Lexing                   *)
(* ------------------------ *)

type token =
  | Kwd of string
  | Ident of string
  | Int of big_int
  | Float of float
  | String of string

let string_of_token t =
  begin match t with
    Kwd(s) -> "Keyword:" ^ s
  | Ident(s) -> "Identifier:" ^ s
  | Int(bi) -> "Int:" ^ (Big_int.string_of_big_int bi)
  | Float(fl) -> "Float:" ^ (string_of_float fl)
  | String(s) -> "String: " ^ s
  end

let keywords = [
  "AST_Wrapper";
  "AST_Annotation";
  "AST_Package"; 
  "AST_Import"; 
  "AST_Enum"; 
  "AST_Interface"; 
  "AST_Class"; 
  "AST_ConstructorDecl"; 
  "AST_MethodDecl"; 
  "AST_VarDecl"; 
  
  "AST_Block"; 
  "AST_ExprStat";
  "AST_DoWhile"; 
  "AST_While"; 
  "AST_For"; 
  "AST_Foreach"; 
  "AST_Labelled"; 
  "AST_Label"; 
  "AST_Switch"; 
  "AST_Case"; 
  "AST_Synchronized"; 
  "AST_Try"; 
  "AST_Catch"; 
  "AST_Cond"; 
  "AST_If"; 
  "AST_Break"; 
  "AST_Continue"; 
  "AST_Return"; 
  "AST_Throw"; 
  "AST_Assert"; 

  "AST_Apply"; 
  "AST_NewClass"; 
  "AST_NewArray"; 
  "AST_Assign"; 
  "AST_AssignOp";  
  "AST_Unary"; 
  "AST_Binary"; 
  "AST_TypeCast"; 
  "AST_TypeTest"; 
  "AST_ArrayAccess";
  "AST_Access"; 
  "AST_Identifier"; 
  "AST_Literal"; 

  "AST_TypeIdent"; 
  "AST_TypeArray"; 
  "AST_TypeApply"; 
  "AST_TypeUnion"; 
  "AST_TypeParameter"; 
  "AST_WildCard"; 
  "AST_TypeBoundKind"; 
  "AST_Modifiers"; 
  
  "AST_AutoGen";

  ":"; "-"; ","; ";"; "("; ")"; "{"; "}"
]

let make_lexer keywords text =
  let buffer = ref "" in
  let append c = buffer := !buffer ^ (String.make 1 c) in
  let reset_buffer () = let b = !buffer in buffer := ""; b in
  let stream = Stream.of_string(text) in
  let next () = Stream.next stream in
  let peek () = 
    match Stream.peek stream with
      Some t -> t
    | None -> '\000'
  in
  let junk () = Stream.junk stream in
  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  
  let ident_or_key () =
    let s = reset_buffer () in
    if Hashtbl.mem kwd_table s then
      Some (Kwd s)
    else
      Some (Ident s)
  in
  let rec make_ident_or_key () =
    match peek () with 
      _ as c when (Hashtbl.mem kwd_table (String.make 1 c)) -> 
            if (String.length !buffer > 0 ) then
              ident_or_key ()
            else
              (junk(); Some (Kwd (String.make 1 c)))
    | ('A'..'Z' | 'a'..'z' | '\128'..'\255' | '0'..'9' | '_' | '\'') as c -> 
            junk (); append c; make_ident_or_key ()
    | (' ' | '\009' | '\010'| '\012'| '\013' | '\026') -> 
            ident_or_key ()
    | _ as c -> error dummy_loc ("Internal Error!\n" ^
                "AST Lexer encountered unexpected character while scanning identifier/keyword: " ^ 
                (String.make 1 c))
  in
  
  let rec make_num () =
    match peek () with
      ('0'..'9' as c) ->
        junk (); append c; make_num ()
    | '.' -> junk (); append '.'; decimal_part ()
    | ('e' | 'E') ->
        junk (); append 'E'; exponent_part ()
    | ('r') ->
        junk (); Some (Float (float_of_string (reset_buffer ())))
    | _ -> Some (Int (big_int_of_string (reset_buffer ())))
  and decimal_part () =
    match peek () with
      ('0'..'9' as c) ->
        junk (); append c; decimal_part ()
    | ('e' | 'E') ->
        junk (); append 'E'; exponent_part ()
    | _ -> Some (Float (float_of_string (reset_buffer ())))
  and exponent_part () =
    match peek () with
      ('+' | '-' as c) ->
        junk (); append c; end_exponent_part ()
    | _ -> end_exponent_part ()
  and end_exponent_part () =
    match peek () with
      ('0'..'9' as c) ->
        junk (); append c; end_exponent_part ()
    | _ -> Some (Float (float_of_string (reset_buffer ())))
  in

  let rec make_string () =
    match next () with 
      '\\' as c -> append c; append (next()); make_string ()
    | '\"' -> let s = reset_buffer () in Some (String s)
    | c -> append c; make_string ()
  in

  let rec next_token () =
    match peek () with
      ('\000'..'\032') -> junk (); next_token ()
    | ('0'..'9' | '.') -> make_num ()
    | ('"') -> junk (); make_string ()
    | ('\033'..'\255') -> make_ident_or_key ()
  in
  Stream.from(
    fun x -> 
      try
        next_token ()
(*        let t = next_token() in
        let s = 
          match t with
            Some t -> string_of_token t
          | None -> "None"
        in
        Printf.printf "<token>%s\n" s;
        t*)
      with
        Stream.Failure -> error dummy_loc ("Internal Failure!\n" ^
                          "AST Lexer aborted with failure")
      | Stream.Error m -> error dummy_loc ("Internal Error!\n" ^
                          "AST Lexer aborted with failure (" ^ m ^ ")")
  )

(* ------------------------ *)
(* Auxilary parse functions *)
(* ------------------------ *)

let parse_int = parser
  [< '(Int i) >] -> Big_int.int_of_big_int i
let parse_big_int = parser
  [< '(Int i) >] -> i
let parse_string = parser
  [< '(String s) >] -> s
let parse_path = parser
  [< '(String s) >] -> split_path s
let parse_srcpos = parser
  [< p = parse_path; '(Kwd "-"); l = parse_int; '(Kwd "-"); c = parse_int >] -> (p,l,c)
let parse_loc = parser
  [< '(Kwd "("); p1 = parse_srcpos; '(Kwd ","); p2 = parse_srcpos; '(Kwd ")") >] -> (p1,p2)
| [<>] -> dummy_loc

let parse_opt p = parser 
  [< result = p >] -> 
    debug_print "parse_opt done (some)"; 
    Some result
| [< >] -> 
    debug_print "parse_opt done (none)"; 
    None
let rec parse_list p = parser
  [< result = p; rest = parse_list p >] -> 
    debug_print "parse_list done (none empty)"; 
    result::rest
| [< >] -> debug_print "parse_list done (empty)";  []

let parse_line_node = parser
    [< 
       '(Kwd ":"); '(String value); l = parse_loc; '(Kwd ";") 
    >] -> (l, value)
let parse_block_node_begin = parser
    [< 
       '(Kwd ":"); '(String value); l = parse_loc; '(Kwd "{") 
    >] -> (l, value)
let parse_block_node_end = parser
    [< '(Kwd "}") >] 
      -> ()
let parse_wrapped wrapped = parser
    [< 
       '(Kwd "AST_Wrapper"); 
       (_, n) = parse_block_node_begin;
       l = parse_list wrapped;
       _ = parse_block_node_end 
    >] -> debug_print ("parse_wrapped done: " ^ n);  l

let filter_mods l mods =
  let filter m =
    if (m = "strictfp") then
      error l "Currentrly unsupported modifier: strictfp"
    else if (m = "volatile") then
      error l "Currentrly unsupported modifier: volatile"
    else if (m = "transient") then
      error l "Currentrly unsupported modifier: transient"
    else if (m = "synchronized") then
      error l "Currentrly unsupported modifier: synchronized"
    else if (m = "native") then
      error l "Currentrly unsupported modifier: native"
  in
  List.iter filter mods 
    
let rec retrieve_accessibility mods =
  if List.mem "public" mods then PublicAccess
  else if List.mem "private" mods then PrivateAccess
  else PackageAccess

let retrieve_abstract mods =
  if (List.mem "abstract" mods) then true else false
let retrieve_final mods =
  if (List.mem "final" mods) then true else false
let retrieve_protected mods =
  if (List.mem "protected" mods) then true else false
let retrieve_static mods =
  if (List.mem "static" mods) then true else false

(* ------------------------ *)
(* Parse functions          *)
(* ------------------------ *)

(* main parse function *)
let rec read_ast s =
  try
(*     Printf.printf "%s" s; *)
    parse_package (make_lexer keywords s)
  with
    Stream.Error m -> 
      let m = 
        "Parsing failed" ^
        (if m <> "" then (": " ^ m) else "")
      in
      raise (AstReaderException(dummy_loc, m))


(* verifier annotations *)
and
  parse_annotation = parser
    [< 
       '(Kwd "AST_Annotation"); 
       (l, _) = parse_block_node_begin; 
       '(String value);
       _ = parse_block_node_end
    >] -> 
      debug_print ("parse_annotation done: " ^ value); 
      Annotation(l, value)


(* names *)
and
  parse_identifier = parser
    [< 
       '(Kwd "AST_Identifier"); 
       (l, value) = parse_line_node;
    >] -> 
      debug_print ("parse_identifier done: " ^ value); 
      Identifier(l, value)
and
  parse_name = parser  
    [< 
       '(Kwd "AST_Access"); 
       (l, _) = parse_block_node_begin;
       name = parse_name;
       id = parse_identifier;
       _ = parse_block_node_end
    >] -> 
      debug_print ("parse_name (name) done: " ^ (string_of_name name)); 
      (match name with 
        Name(_, parts) ->
          Name(l, List.append parts [id]))
  | [< 
       Identifier(l, value) = parse_identifier
    >] -> 
      debug_print ("parse_name (identifier) done: " ^ value);
      Name(l, [Identifier(l,value)])


(* accessibility modifiers *)
and
  parse_modifiers = parser
    [< 
       '(Kwd "AST_Modifiers"); 
       (l, value) = parse_line_node 
    >] ->
      debug_print ("parse_modifiers done: " ^ value); 
      let mods = split_string ' ' value in
      filter_mods l mods;
      mods


(* types *)
and
  parse_prim_type = parser
    [< 
       '(Kwd "AST_TypeIdent"); 
       (l, name) = parse_line_node;
    >] ->
      debug_print ("parse_prim_type done: " ^ name); 
      prim_type_of_string l name
and
  parse_ref_type = parser
    [< name = parse_name >] -> debug_print "parse_ref_type (simple) done"; SimpleRef(name)
  | [< 
       '(Kwd "AST_TypeApply"); 
       (l, _) = parse_block_node_begin;
       name = parse_name;
       args = parse_wrapped parse_ref_type;
       _ = parse_block_node_end
    >] -> 
       debug_print "parse_ref_type (apply) done"; TypeApply(l, name, args)
and
  parse_type = parser
    [< t = parse_prim_type >] -> debug_print "parse_type (prim) done"; PrimType(t)
  | [< t = parse_ref_type >] -> debug_print "parse_type (ref) done"; RefType(t)
(*  | [< name = parse_name >] -> 
         debug_print "parse_type (simple ref) done"; RefType(SimpleRef(name))*)
  | [< '(Kwd "AST_TypeArray"); 
       _ = parse_block_node_begin;
       t = parse_ref_type; 
       _ = parse_block_node_end
    >] -> debug_print "parse_type (array) done"; ArrayType(t)
and
  parse_type_param = parser
    [< 
       '(Kwd "AST_TypeParameter"); 
       (l, id) = parse_block_node_begin;
       bounds = parse_list parse_ref_type;
       _ = parse_block_node_end
    >] -> 
       debug_print "parse_type_param done"; TypeParam(l, Identifier(l,id), bounds)


(* package level *)
and
  parse_package = parser
    [< 
       '(Kwd "AST_Package"); 
       (l, _) = parse_block_node_begin;
       name   = parse_opt parse_name;
       imprts = parse_list parse_import; 
       decls  = parse_list parse_package_decl;
       _      = parse_block_node_end 
    >] -> 
      let name = 
        match name with 
          Some x -> x
        | None -> dummy_name
      in
      debug_print ("parse_package done: " ^ (string_of_name name)); 
      Package(l, name, imprts, decls)
and
  parse_import = parser
    [< 
       '(Kwd "AST_Import"); 
       (l, _) = parse_block_node_begin ;
       name   = parse_name;
       _      = parse_block_node_end
    >] -> 
      let (pckge, id) = remove_last_id name in
      let id = match id with Identifier(_, "*") -> None | _ -> Some id in
      debug_print ("parse_import done: " ^ (string_of_name name));
      Import(l, pckge, id)
and
  parse_package_decl = parser
    [< ann = parse_annotation >] -> 
      debug_print "parse_package_decl (annot) done"; 
      P_Annotation ann
  | [< inter = parse_interface >] -> 
      debug_print "parse_package_decl (inter) done"; 
      P_Class inter
  | [< cl = parse_class >] -> 
      debug_print "parse_package_decl (class) done"; 
      P_Class cl
  | [< enum = parse_enum >] -> 
      debug_print "parse_package_decl (enum) done"; 
      P_Class enum


(* class level *)
and
  parse_class = parser
    [< 
       '(Kwd "AST_Class"); 
       (l, _) = parse_block_node_begin; 
       id = parse_identifier;
       anns = parse_list parse_annotation;
       tparams = parse_wrapped parse_type_param;
       mods = parse_modifiers;
       extnds = parse_wrapped parse_ref_type;
       inters = parse_wrapped parse_ref_type;
       decls = parse_list parse_class_decl;
       _ = parse_block_node_end 
    >] ->  
      debug_print "parse_class done"; 
      let extnds =
        if List.length extnds > 0 then
          Some (List.hd extnds)
        else
          None
      in
      Class(l, anns, id, tparams,
            retrieve_accessibility mods, 
            retrieve_abstract mods, 
            retrieve_final mods, 
            retrieve_static mods,
            extnds, inters, decls)
and
  parse_interface = parser
    [< 
       '(Kwd "AST_Interface"); 
       (l, _) = parse_block_node_begin; 
       id = parse_identifier;
       anns = parse_list parse_annotation;
       tparams = parse_wrapped parse_type_param;
       mods = parse_modifiers; 
       inters = parse_wrapped parse_ref_type;
       decls = parse_list parse_class_decl;
       _ = parse_block_node_end 
    >] ->  
      debug_print "parse_interface done"; 
      Interface(l, anns, id, tparams, retrieve_accessibility mods, inters, decls)
and
  parse_enum = parser      
    [< 
       '(Kwd "AST_Enum"); 
       (l, _) = parse_block_node_begin; 
       id = parse_identifier;
       anns = parse_list parse_annotation;
       tparams = parse_wrapped parse_type_param;
       mods = parse_modifiers;
       inters = parse_wrapped parse_ref_type;
       decls = parse_list (parse_enum_decl l id);
       _ = parse_block_node_end 
    >] -> 
      if (List.length tparams > 0) then 
        error l "Enums with type params are currently not supported by Java frontend";
      if (List.length inters > 0) then 
        error l ("Enums that implement an interface are currently not supported by Java frontend");
      debug_print "parse_enum done"; 
      Enum(l, anns, id, retrieve_accessibility mods, List.concat decls)
and
  parse_enum_decl l id = parser
    [< var = parse_var_decl >] ->
      let vid = 
        match var with 
          Variable(l, vid, access, prot, final, stat, typ, init) -> 
            if (access <> PublicAccess) then 
              error l "Enumerators should be public";
            if (prot) then 
              error l "Enumerators should not be protected";
            if (not final) then 
              error l "Enumerators should be final";
            if (not stat) then 
              error l "Enumerators should be static";
            if (string_of_type typ <> string_of_identifier id) then 
              error l "Enumerators should have the type of their enumeration";
            (match init with 
              Some(NewClass(_, [], _, [])) -> vid
            | _ -> error l ("Enumerators cannot have an initializing expression" ^
                                      "(except invocation of the default constructor)"));
      in
      debug_print ("parse_enum_value done: " ^ (string_of_identifier vid)); [vid]
  | [< decl = parse_class_decl >] ->
      match decl with
        C_Method(Constructor(_, _, id, [], _, _, [], [], _, _)) 
          when string_of_identifier id = "<init>"-> []
      | _ -> error l ("Enums that contain method (including constructors) or instance" ^ 
                      "variable declarations are currently not supported by Java frontend")
and
  parse_class_decl = parser
    [< var = parse_var_decl >]    -> debug_print "parse_class_decl (var) done"; C_Variable var
  | [< meth = parse_meth_decl >]  -> debug_print "parse_class_decl (meth) done"; C_Method meth
  | [< ann = parse_annotation >]  -> debug_print "parse_class_decl (ann) done"; C_Annotation ann
  | [< inter = parse_interface >] -> debug_print "parse_class_decl (inter) done"; C_Class inter
  | [< cl = parse_class >]        -> debug_print "parse_class_decl (cl) done"; C_Class cl
  | [< enum = parse_enum >]       -> debug_print "parse_class_decl (enum) done"; C_Class enum  
and
  parse_meth_decl = parser
    [< 
       '(Kwd "AST_ConstructorDecl"); 
       (l, _) = parse_block_node_begin;
       id = parse_identifier;
       anns = parse_list parse_annotation;
       tparams = parse_wrapped parse_type_param;
       mods = parse_modifiers;
       params = parse_wrapped parse_var_decl;
       thrown_exceptions = parse_wrapped parse_ref_type;
       thrown_annotations = parse_wrapped parse_annotation; 
       (_, stmts) = parse_block_as_stmts; 
       auto_gen = parse_auto_gen;
       _ = parse_block_node_end 
    >] -> 
      debug_print ("parse_meth_decl (cons) done: " ^ (string_of_identifier id));
      let thrown = List.map2 (fun x y -> (x, y)) thrown_exceptions thrown_annotations in
      Constructor(l, anns, id, tparams, 
                  retrieve_accessibility mods,
                  retrieve_protected mods,  
                  params, thrown, stmts, auto_gen)
  | [< 
       '(Kwd "AST_MethodDecl"); 
       (l, name) = parse_block_node_begin;
       id = parse_identifier;
       anns = parse_list parse_annotation;
       tparams = parse_wrapped parse_type_param;
       mods = parse_modifiers;
       rett = parse_type;
       params = parse_wrapped parse_var_decl;
       thrown_exceptions = parse_wrapped parse_ref_type;
       thrown_annotations = parse_wrapped parse_annotation; 
       body = parse_block_as_opt;
       _ = parse_block_node_end 
    >] ->
      debug_print ("parse_meth_decl (meth) done: " ^ (string_of_identifier id));
      let thrown = List.map2 (fun x y -> (x, y)) thrown_exceptions thrown_annotations in
      Method(l, anns, id, tparams, 
             retrieve_accessibility mods,
             retrieve_protected mods,  
             retrieve_abstract mods, 
             retrieve_final mods,  
             retrieve_static mods,
             rett, params, thrown, body)
and
  parse_var_decl = parser
    [< 
       '(Kwd "AST_VarDecl"); 
       (l, _) = parse_block_node_begin;
       id = parse_identifier;
       mods = parse_modifiers;
       typ = parse_type;
       init = parse_opt parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print ("parse_var_decl done: " ^ (string_of_identifier id));
      Variable(l, id, retrieve_accessibility mods,
               retrieve_protected mods, 
               retrieve_final mods, 
               retrieve_static mods,
               typ, init)
and
  parse_auto_gen = parser [<
      ag = parse_opt (parser [< '(Kwd "AST_AutoGen"); _ = parse_line_node >] -> ())
    >] -> match ag with
            Some _ -> true
          | None -> false
          
(* statements *)
and
  parse_block_as_opt = parser
    [< 
       '(Kwd "AST_Block"); 
       _ = parse_block_node_begin;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_block (none empty) done";
      Some stmts
  | [<>] -> debug_print "parse_block (empty) done"; None
and
  parse_block_as_stmts = parser
    [< 
       '(Kwd "AST_Block"); 
       (l, _) = parse_block_node_begin;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_block_as_stmts";
      (l, stmts)
and
  parse_statement = parser
    [< ann = parse_annotation >] ->
      debug_print "parse_statement (Annotation) done";
      S_Annotation(ann)   
  | [< var = parse_var_decl >] ->
      debug_print "parse_statement (Variable) done";
      S_Variable(var)
  | [< expr = parse_expression >] ->
      debug_print "parse_statement (Expression) done";
      S_Expression(expr)
  | [< (l, stmts) = parse_block_as_stmts >] ->
      debug_print "parse_statement (Block) done";
      Block(l, stmts)
  | [< 
       '(Kwd "AST_Try"); 
       (l, _) = parse_block_node_begin; 
       (_, stmts) = parse_block_as_stmts;
       catchs = parse_wrapped parse_catch_block;
       _ = parse_block_node_end 
    >] -> 
      debug_print "parse_statement (Try) done";
      Try(l, stmts, catchs) 
  | [< 
       '(Kwd "AST_DoWhile"); 
       (l, _) = parse_block_node_begin;
       anns = parse_list parse_annotation;
       cond = parse_expression;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (DoWhile) done";
      DoWhile(l, anns, cond, stmts)
  | [< 
       '(Kwd "AST_While"); 
       (l, _) = parse_block_node_begin;
       anns = parse_list parse_annotation;
       cond = parse_expression;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (While) done";
      While(l, anns, cond, stmts)
  | [< 
       '(Kwd "AST_For"); 
       (l, _) = parse_block_node_begin;
       anns = parse_list parse_annotation;
       init = parse_wrapped parse_statement;
       cond = parse_expression;
       up = parse_wrapped parse_statement;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (For) done";
      For(l, anns, init, cond, up, stmts)
  | [< 
       '(Kwd "AST_Foreach"); 
       (l, _) = parse_block_node_begin;
       anns  = parse_list parse_annotation;
       var   = parse_var_decl;
       iter  = parse_expression;
       stmts = parse_list parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (Foreach) done";
      Foreach(l, anns, var, iter, stmts)
  | [< 
       '(Kwd "AST_If"); 
       (l, _) = parse_block_node_begin;
       cond = parse_expression;
       if_ = parse_statement;
       else_ = parse_statement;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (If) done";
      If(l, cond, if_, else_)
  | [< 
       '(Kwd "AST_Return"); 
       (l, _) = parse_block_node_begin;
       expr = parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (Return) done";
      Return(l, expr)
  | [< 
       '(Kwd "AST_Throw"); 
       (l, _) = parse_block_node_begin;
       expr = parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_statement (Throw) done";
      Throw(l, expr)
  
and parse_catch_block = parser
  | [< 
       '(Kwd "AST_Catch"); 
       (l, _) = parse_block_node_begin; 
       excep = parse_var_decl;
       (_, stmts) = parse_block_as_stmts;
       _ = parse_block_node_end 
    >] -> 
       debug_print "parse_catch_block";
       Catch(l, excep, stmts)

(* expressions *)
and
  parse_expression = parser
  | [< id = parse_identifier >] ->
      debug_print "parse_expression (Identifier) done";
      E_Identifier(id)
  | [< 
       '(Kwd "AST_Access"); 
       (l, _) = parse_block_node_begin;
       exp = parse_expression;
       id =  parse_identifier;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_expression (Access) done";
      Access(l, exp, id)
  | [< 
       '(Kwd "AST_Apply"); 
       (l, _) = parse_block_node_begin;
       tparams = parse_wrapped parse_type_param;
       exp = parse_expression;
       args = parse_wrapped parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_expression (Apply) done";
      Apply(l, tparams, exp, args)
  | [< 
       '(Kwd "AST_NewClass"); 
       (l, _) = parse_block_node_begin;
       tparams = parse_wrapped parse_type_param;
       typ = parse_ref_type;
       args = parse_wrapped parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print ("parse_expression (NewClass) done: " ^ (string_of_ref_type typ));
      NewClass(l, tparams, typ, args)
  | [< 
       '(Kwd "AST_NewArray"); 
       (l, _) = parse_block_node_begin; 
       typ   = parse_type;
       (* TODO: fix correct parsing of dimentions*)
       _ = parse_wrapped parse_expression;
       elem  = parse_wrapped parse_expression;
       _ = parse_block_node_end 
    >] -> debug_print "AST_NewArray";
          NewArray(l, typ, elem)
          
  | [< 
       '(Kwd "AST_Assign"); 
       (l, _) = parse_block_node_begin;
       (* TODO:parse possible bin operator *)
       lhs = parse_expression;
       rhs = parse_expression;
       _ = parse_block_node_end 
    >] ->
      debug_print "parse_expression (Assign) done";
      Assign(l, None, lhs, rhs)
  | [< 
       '(Kwd "AST_Unary"); 
       (l,op) = parse_block_node_begin; 
       expr = parse_expression;
       _ = parse_block_node_end 
    >] -> 
      debug_print ("parse_expression (Unary) done: " ^ op);
      Unary(l, (u_operator_of_string op), expr)
  | [< 
       '(Kwd "AST_Binary"); 
       (l,op) = parse_block_node_begin; 
       lhs = parse_expression;
       rhs = parse_expression;
       _ = parse_block_node_end 
    >] -> 
      debug_print ("parse_expression (Unary) done: " ^ op);
      Binary(l, (b_operator_of_string op), lhs, rhs)
  | [< 
       '(Kwd "AST_Literal"); 
       (l,typ) = parse_block_node_begin; 
       value = parse_string;
       _ = parse_block_node_end 
    >] -> 
      debug_print ("parse_expression (Literal) done: " ^ value);
      if typ <> "string" && typ <> "ref" then
        Literal(l, PrimType(prim_type_of_string l typ), value)
      else if typ <> "ref" then
        Literal(l, RefType(SimpleRef(Name(l, [Identifier(l, "String")]))), value)
      else
        Literal(l, RefType(SimpleRef(Name(l, []))), "null")
  | [< 
      '(Kwd "AST_TypeCast"); 
      (l,_) = parse_block_node_begin; 
      t = parse_type;
      e = parse_expression;
      _ = parse_block_node_end 
    >] -> 
      debug_print "parse_expression (TypeCast) done";
      TypeCast(l, t, e)
end
