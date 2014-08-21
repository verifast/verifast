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

exception AstReaderException of source_location * string
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
  | Int of big_int
  | Float of float
  | String of string

let string_of_token t =
  begin match t with
    Kwd(s) -> "Keyword:" ^ s
  | Int(bi) -> "Int:" ^ (Big_int.string_of_big_int bi)
  | Float(fl) -> "Float:" ^ (string_of_float fl)
  | String(s) -> "String: " ^ s
  end

let keywords = [
  (* General *)
  "None";
  "Some";
  
  (* source locations *)
  "NoSource";
  "SourceLine";
  "SourceLines";
  "Original";
  "Generated";

  (* verifier annotations *)
  "Annotation";

  (* names *)
  "Identifier";
  "Name";

  (* accessibility modifiers *)
  "PublicAccess";
  "PackageAccess";
  "PrivateAccess";
  "ProtectedAccess";
  "Static";
  "NonStatic";
  "Abstract";
  "NonAbstract";
  "Final";
  "NonFinal";

  (* types *)
  "VoidType";
  "BoolType";
  "CharType";
  "ByteType";
  "ShortType";
  "IntType";
  "LongType";
  "FloatType";
  "DoubleType";
  "SimpleRef";
  "TypeApply";
  "Wildcard";
  "Upper";
  "Lower";
  "PrimType";
  "RefType";
  "ArrayType";
  "TypeParam";

  (* package level *)
  "Package";
  "Import";
  "P_Annotation";
  "P_Class";

  (* class level *)
  "Class";
  "Interface";
  "Enum";
  "Field";
  "C_Method";
  "C_Annotation";
  "C_Class";
  "Constructor";
  "Method";
  "StaticBlock";
  "Variable";
  
  (* statements *)
  "S_Annotation";
  "S_Variable";
  "S_Expression";
  "Block";
  "Try";
  "DoWhile";
  "While";
  "For";
  "Foreach";
  "Labeled";
  "Switch";
  "If";
  "Break";
  "Continue";
  "Return";
  "Throw";
  "Assert";
  "Case";
  "Catch";

  (* expressions *)
  "E_Identifier";
  "Access";
  "Apply";
  "NewClass";
  "NewArray";
  "Assign";
  "Unary";
  "Binary";
  "Ternary";
  "TypeCast";
  "TypeTest";
  "ArrayAccess";
  "Literal";
  
  (* bin_operator *)
  "O_Plus";
  "O_Min";
  "O_Mul";
  "O_Div";
  "O_Mod";
  "O_Or";
  "O_And";
  "O_Eq";
  "O_NotEq";
  "O_Lt";
  "O_Gt";
  "O_LtEq";
  "O_GtEq";
  "O_BitOr";
  "O_BitXor";
  "O_BitAnd";
  "O_ShiftL";
  "O_ShiftR";
  "O_UShiftR";

  (* uni_operator *)
  "O_Pos";
  "O_Neg";
  "O_Not";
  "O_Compl";
  "O_PreInc";
  "O_PreDec";
  "O_PostInc";
  "O_PostDec";

  ","; ";"; "("; ")"; "["; "]";
]

let make_lexer keywords lines =
  let buffer = ref "" in
  let append c = buffer := !buffer ^ (String.make 1 c) in
  let reset_buffer () = let b = !buffer in buffer := ""; b in
  let str = 
    try
      join_lines_fail lines
    with Invalid_argument(_) ->
    begin
      let lines' = List.map Misc.trim lines in
      try
        String.concat "" lines'
      with Invalid_argument(_) ->
        error NoSource ("Input was to big")
    end
  in
  let stream = Stream.of_string str in
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
      error NoSource ("Internal Error: \"" ^ s ^ "\" is not a valid keyword")
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
    | (' ' | '\000' | '\009' | '\010'| '\012'| '\013' | '\026') -> 
            ident_or_key ()
    | _ as c -> error NoSource ("Internal Error!\n" ^
                "AST Lexer encountered unexpected character while scanning identifier/keyword " ^
                !buffer ^ " : " ^ (Printf.sprintf "%i" (int_of_char c)))
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
        Stream.Failure -> error NoSource ("Internal Failure!\n" ^
                          "AST Lexer aborted with failure")
      | Stream.Error m -> error NoSource ("Internal Error!\n" ^
                          "AST Lexer aborted with failure (" ^ m ^ ")")
  )

(* ------------------------ *)
(* Auxilary parse functions *)
(* ------------------------ *)

(* general stuff *)
let parse_int = parser [< '(Int i) >] -> 
      debug_print ("parse_int " ^ (string_of_big_int i)); int_of_big_int i
let parse_float = parser [< '(Float f) >] -> 
      debug_print ("parse_float " ^ (string_of_float f));f
let parse_string = parser [< '(String s) >] -> 
      debug_print ("parse_string " ^ s); s
let parse_list : (token Stream.t -> 'a) -> (token Stream.t) -> 'a list =
  fun p ->
    let rec parse_rest = parser
        | [< '(Kwd ";"); result = p; rest = parse_rest >] -> result::rest
        | [< >] -> []
    in
    let rec parse_list_core = parser
        | [< result = p; rest = parse_rest >] -> debug_print "parse_list Cons"; result::rest
        | [< >] -> debug_print "parse_list Nil"; []
    in
    parser
      | [< '(Kwd "["); result = parse_list_core; '(Kwd "]"); >] -> result
let parse_pair : (token Stream.t -> 'a) -> (token Stream.t -> 'b) -> 
                             (token Stream.t) -> ('a * 'b) = 
  fun p1 p2 -> parser
  | [< '(Kwd "("); p1' = p1; '(Kwd ","); p2' = p2; '(Kwd ")") >] -> 
      debug_print "parse_pair"; (p1', p2')
let parse_opt : (token Stream.t -> 'a) -> (token Stream.t) -> 'a option =
  fun p -> parser 
  | [< '(Kwd "Some"); '(Kwd "("); result = p; '(Kwd ")") >] -> 
      debug_print "parse_opt Some"; Some result
  | [< '(Kwd "None") >] -> 
      debug_print "parse_opt None"; None

(* ------------------------ *)
(* Main functions           *)
(* ------------------------ *)

let parse_with p s =
  try
    p (make_lexer keywords s)
  with
    Stream.Error m -> 
      let m = 
        "Parsing failed" ^
        (if m <> "" then (": " ^ m) else "")
      in
      error NoSource m

let parse_line_with p s = parse_with p [s]

let rec read_asts s =
  parse_with (parse_list parse_package) s

(* ------------------------ *)
(* AST Parse functions      *)
(* ------------------------ *)

(* locations *)
and 
  parse_loc = parser
  | [< '(Kwd "NoSource") >] -> 
      debug_print ("parse_loc: " ^ "NoSource");
      NoSource
  | [< '(Kwd "SourceLine"); '(Kwd "("); 
          f = parse_string; '(Kwd ","); 
          l = parse_int;    '(Kwd ","); 
          c1 = parse_int;   '(Kwd ","); 
          c2 = parse_int;   '(Kwd ")");
    >] -> 
      debug_print ("parse_loc: " ^ "SourceLine");
      SourceLine(f, l, c1, c2)
  | [< '(Kwd "SourceLines"); '(Kwd "("); 
          f = parse_string;  '(Kwd ","); 
          l1 = parse_int;    '(Kwd ","); 
          c1 = parse_int;    '(Kwd ","); 
          l2 = parse_int;    '(Kwd ","); 
          c2 = parse_int;    '(Kwd ")"); 
    >] -> 
      debug_print ("parse_loc: " ^ "SourceLines");
      SourceLines(f, l1, c1, l2, c2)
and
  parse_gen_source = parser
  | [< '(Kwd "Original") >]  -> debug_print ("parse_source: Original");  Original
  | [< '(Kwd "Generated") >] -> debug_print ("parse_source: Generated"); Generated


(* verifier annotations *)
and
  parse_annotation = parser
  | [< '(Kwd "Annotation");    '(Kwd "("); 
          l = parse_loc;       '(Kwd ","); 
          v = parse_string;    '(Kwd ")"); 
    >] -> 
      debug_print ("parse_annotation: " ^ v);
      Annotation(l, v)


(* names *)
and
  parse_identifier = parser
  | [< '(Kwd "Identifier");    '(Kwd "("); 
          l = parse_loc;       '(Kwd ","); 
          i = parse_string;    '(Kwd ")"); 
    >] -> 
      debug_print ("parse_identifier: " ^ i);
      Identifier(l, i)
and
  parse_name = parser  
  | [< '(Kwd "Name");                        '(Kwd "("); 
          l = parse_loc;                     '(Kwd ","); 
          ids = parse_list parse_identifier; '(Kwd ")"); 
    >] -> 
      debug_print ("parse_name");
      Name(l, ids)


(* accessibility *)
and
  parse_accessibility = parser
  | [< '(Kwd "PublicAccess") >]    -> debug_print ("parse_accessibility: PublicAccess");    PublicAccess
  | [< '(Kwd "PrivateAccess") >]   -> debug_print ("parse_accessibility: PrivateAccess");   PrivateAccess
  | [< '(Kwd "PackageAccess") >]   -> debug_print ("parse_accessibility: PackageAccess");   PackageAccess
  | [< '(Kwd "ProtectedAccess") >] -> debug_print ("parse_accessibility: ProtectedAccess"); ProtectedAccess
and
  parse_static_binding = parser
  | [< '(Kwd "Static") >]    -> debug_print ("parse_static_binding: Static");    Static
  | [< '(Kwd "NonStatic") >] -> debug_print ("parse_static_binding: NonStatic"); NonStatic
and
  parse_abstractness = parser
  | [< '(Kwd "Abstract") >]    -> debug_print ("parse_abstractness: Abstract");    Abstract
  | [< '(Kwd "NonAbstract") >] -> debug_print ("parse_abstractness: NonAbstract"); NonAbstract
and
  parse_finality = parser
  | [< '(Kwd "Final") >]    -> debug_print ("parse_finality: Final");    Final
  | [< '(Kwd "NonFinal") >] -> debug_print ("parse_finality: NonFinal"); NonFinal


(* types *)
and
  parse_prim_type = parser
  | [< '(Kwd "VoidType");  '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: VoidType"); VoidType(l)
  | [< '(Kwd "BoolType");  '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: BoolType"); BoolType(l)
  | [< '(Kwd "CharType");  '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: CharType"); CharType(l)
  | [< '(Kwd "ByteType");  '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: ByteType"); ByteType(l)
  | [< '(Kwd "ShortType"); '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: ShortType"); ShortType(l)
  | [< '(Kwd "IntType");   '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: IntType"); IntType(l)
  | [< '(Kwd "LongType");  '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: LongType"); LongType(l)
  | [< '(Kwd "FloatType"); '(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: FloatType"); FloatType(l)
  | [< '(Kwd "DoubleType");'(Kwd "("); 
       l = parse_loc; '(Kwd ")") >] -> debug_print ("parse_prim_type: DoubleType"); DoubleType(l)
and
  parse_ref_type = parser
  | [< '(Kwd "SimpleRef"); '(Kwd "("); 
          n = parse_name;  '(Kwd ")"); 
    >] -> 
      debug_print ("parse_ref_type: SimpleRef");
      SimpleRef(n)
  | [< '(Kwd "TypeApply");                  '(Kwd "(");
          l = parse_loc;                    '(Kwd ",");
          n = parse_name;                   '(Kwd ",");
          typs = parse_list parse_ref_type; '(Kwd ")");
    >] -> 
      debug_print ("parse_ref_type: TypeApply");
      TypeApply(l, n, typs)
  | [< '(Kwd "WildCard");                 '(Kwd "(");
          l = parse_loc;                  '(Kwd ",");
          typ = parse_opt parse_ref_type; '(Kwd ",");
          bound = parse_type_bound;       '(Kwd ")");
          
    >] -> 
      debug_print ("parse_ref_type: WildCard");
      WildCard(l, typ, bound)
and
  parse_type_bound = parser
  | [< '(Kwd "Upper") >]   -> debug_print ("parse_type_bound: Upper");   Upper
  | [< '(Kwd "Lower") >]   -> debug_print ("parse_type_bound: Lower");   Lower
  | [< '(Kwd "Unbound") >] -> debug_print ("parse_type_bound: Unbound"); Unbound
and
  parse_type = parser
  | [< '(Kwd "PrimType");      '(Kwd "(");
          t = parse_prim_type; '(Kwd ")");
    >] -> 
      debug_print ("parse_type: PrimType");
      PrimType(t)
  | [< '(Kwd "RefType");      '(Kwd "(");
          t = parse_ref_type; '(Kwd ")");
    >] -> 
      debug_print ("parse_type: RefType");
      RefType(t)
  | [< '(Kwd "ArrayType");    '(Kwd "(");
          t = parse_type;     '(Kwd ")");
    >] -> 
      debug_print ("parse_type: ArrayType");
      ArrayType(t)
and
  parse_type_param = parser
  | [< '(Kwd "TypeParam");                  '(Kwd "(");
          l = parse_loc;                    '(Kwd ",");
          id = parse_identifier;            '(Kwd ",");
          typs = parse_list parse_ref_type; '(Kwd ")");
    >] -> 
      debug_print ("parse_type_param: TypeParam");
      TypeParam(l, id, typs)


(* package level *)
and
  parse_package = parser
  | [< '(Kwd "Package");                          '(Kwd "(");
          l = parse_loc;                          '(Kwd ",");
          n = parse_name;                         '(Kwd ",");
          imprts = parse_list parse_import;       '(Kwd ","); 
          decls  = parse_list parse_package_decl; '(Kwd ")");
    >] -> 
      debug_print ("parse_package: Package");
      Package(l, n, imprts, decls)
and
  parse_import = parser
  | [< '(Kwd "Import");                    '(Kwd "(");
          l = parse_loc;                   '(Kwd ",");
          p = parse_name;                  '(Kwd ",");
          id = parse_opt parse_identifier; '(Kwd ")");
    >] -> 
      debug_print ("parse_import: Import");
      Import(l, p, id)
and
  parse_package_decl = parser
  | [< '(Kwd "P_Annotation");   '(Kwd "(");
          a = parse_annotation; '(Kwd ")");
    >] -> 
      debug_print "parse_package_decl: P_Annotation"; 
      P_Annotation(a)
  | [< '(Kwd "P_Class");                  '(Kwd "(");
          c = parse_class_interface_enum; '(Kwd ")");
    >] -> 
      debug_print "parse_package_decl: P_Class"; 
      P_Class(c)


(* class level *)
and
  parse_class_interface_enum = parser
  | [< '(Kwd "Class");                           '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          anns = parse_list parse_annotation;    '(Kwd ",");
          id = parse_identifier;                 '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          access = parse_accessibility;          '(Kwd ",");
          abs = parse_abstractness;              '(Kwd ",");
          final = parse_finality;                '(Kwd ",");
          static = parse_static_binding;         '(Kwd ",");
          extnds = parse_opt parse_ref_type;     '(Kwd ",");
          inters = parse_list parse_ref_type;    '(Kwd ",");
          decls = parse_list parse_class_decl;   '(Kwd ")");
          
    >] -> 
      debug_print "parse_class_interface_enum: Class"; 
      Class(l, anns, id, tparams, access, abs, final, 
            static, extnds, inters, decls)
  | [< '(Kwd "Interface");                       '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          anns = parse_list parse_annotation;    '(Kwd ",");
          id = parse_identifier;                 '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          access = parse_accessibility;          '(Kwd ",");
          inters = parse_list parse_ref_type;    '(Kwd ",");
          decls = parse_list parse_class_decl;   '(Kwd ")");
          
    >] -> 
      debug_print "parse_class_interface_enum: Interface"; 
      Interface(l, anns, id, tparams, access, inters, decls)
  | [< '(Kwd "Enum");                            '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          anns = parse_list parse_annotation;    '(Kwd ",");
          id = parse_identifier;                 '(Kwd ",");
          access = parse_accessibility;          '(Kwd ",");
          ids = parse_list parse_identifier;     '(Kwd ")");
          
    >] -> 
      debug_print "parse_class_interface_enum: Enum"; 
      Enum(l, anns, id, access, ids)
and
  parse_class_decl = parser
  | [< '(Kwd "C_Annotation");   '(Kwd "(");
          a = parse_annotation; '(Kwd ")");
    >] -> 
      debug_print "parse_class_decl: C_Annotation"; 
      C_Annotation(a)
  | [< '(Kwd "C_Class");                  '(Kwd "(");
          c = parse_class_interface_enum; '(Kwd ")");
    >] -> 
      debug_print "parse_class_decl: C_Class"; 
      C_Class(c)
  | [< '(Kwd "StaticBlock");                  '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_class_decl: StaticBlock"; 
      StaticBlock(l, stmts)
  | [< '(Kwd "Field");                    '(Kwd "(");
          l = parse_loc;                  '(Kwd ",");
          id = parse_identifier;          '(Kwd ",");
          access = parse_accessibility;   '(Kwd ",");
          final = parse_finality;         '(Kwd ",");
          stat = parse_static_binding;    '(Kwd ",");
          typ = parse_type;               '(Kwd ",");
          e = parse_opt parse_expression; '(Kwd ",");
          auto_gen = parse_gen_source;    '(Kwd ")");
          
    >] -> 
      debug_print "parse_class_decl: Field"; 
      Field(l, id, access, final, stat, typ, e, auto_gen)
  | [< '(Kwd "Constructor");                     '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          anns = parse_list parse_annotation;    '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          access = parse_accessibility;          '(Kwd ",");
          params = parse_list parse_var_decl;    '(Kwd ",");
          thrown = parse_list (parse_pair 
             parse_ref_type 
             (parse_opt parse_annotation));      '(Kwd ",");
          stmts = parse_opt (parse_list
             parse_statement);                   '(Kwd ",");
          auto_gen = parse_gen_source;           '(Kwd ")");
    >] -> 
      debug_print ("parse_meth_decl: Constructor");
      Constructor(l, anns, tparams, access, 
                    params, thrown, stmts, auto_gen)
  | [< '(Kwd "Method");                          '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          anns = parse_list parse_annotation;    '(Kwd ",");
          id = parse_identifier;                 '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          access = parse_accessibility;          '(Kwd ",");
          abs = parse_abstractness;              '(Kwd ",");
          final = parse_finality;                '(Kwd ",");
          static = parse_static_binding;         '(Kwd ",");
          rett = parse_type;                     '(Kwd ",");
          params = parse_list parse_var_decl;    '(Kwd ",");
          thrown = parse_list (parse_pair 
             parse_ref_type 
             (parse_opt parse_annotation));      '(Kwd ",");
          stmts = parse_opt (parse_list 
             parse_statement);                   '(Kwd ",");
          auto_gen = parse_gen_source;           '(Kwd ")");
    >] ->
      debug_print ("parse_meth_decl: Method"  ^ (string_of_identifier id));
      Method(l, anns, id, tparams, access, abs, final, 
             static, rett, params, thrown, stmts, auto_gen)
and
  parse_var_decl = parser
  | [< '(Kwd "Variable");                    '(Kwd "(");
          l = parse_loc;                     '(Kwd ",");
          id = parse_identifier;             '(Kwd ",");
          typ = parse_type;                  '(Kwd ",");
          init = parse_opt parse_expression; '(Kwd ")");
    >] ->
      debug_print ("parse_var_decl: Variable"  ^ (string_of_identifier id));
      Variable(l, id, typ, init)


(* statements *)
and
  parse_statement = parser
  | [< '(Kwd "S_Annotation");   '(Kwd "(");
          a = parse_annotation; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: S_Annotation"; 
      S_Annotation(a)
  | [< '(Kwd "S_Variable");   '(Kwd "(");
          v = parse_var_decl; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: S_Variable"; 
      S_Variable(v)
  | [< '(Kwd "S_Expression");   '(Kwd "(");
          e = parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: S_Expression"; 
      S_Expression(e)
  | [< '(Kwd "Block");                        '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Block"; 
      Block(l, stmts)
  | [< '(Kwd "Try");                             '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          stmts = parse_list parse_statement;    '(Kwd ",");
          catchs = parse_list parse_catch_block; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Try"; 
      Try(l, stmts, catchs) 
  | [< '(Kwd "DoWhile");                      '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          anns = parse_list parse_annotation; '(Kwd ",");
          cond = parse_expression;            '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: DoWhile"; 
      DoWhile(l, anns, cond, stmts)
  | [< '(Kwd "While");                        '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          anns = parse_list parse_annotation; '(Kwd ",");
          cond = parse_expression;            '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: While"; 
      While(l, anns, cond, stmts)
  | [< '(Kwd "For");                          '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          anns = parse_list parse_annotation; '(Kwd ",");
          init = parse_list parse_statement;  '(Kwd ",");
          cond = parse_expression;            '(Kwd ",");
          up = parse_list parse_statement;    '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: For"; 
      For(l, anns, init, cond, up, stmts)
  | [< '(Kwd "Foreach");                      '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          anns = parse_list parse_annotation; '(Kwd ",");
          var   = parse_var_decl;             '(Kwd ",");
          iter  = parse_expression;           '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Foreach"; 
      Foreach(l, anns, var, iter, stmts)
  | [< '(Kwd "Labeled");          '(Kwd "(");
          l = parse_loc;          '(Kwd ",");
          id = parse_identifier;  '(Kwd ",");
          stmt = parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Labeled"; 
      Labeled(l, id, stmt)
  | [< '(Kwd "Switch");                   '(Kwd "(");
          l = parse_loc;                  '(Kwd ",");
          sel = parse_expression;         '(Kwd ",");
          cases = parse_list parse_case;  '(Kwd ",");
          default = parse_opt parse_case; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Switch"; 
      Switch(l, sel, cases, default)
  | [< '(Kwd "If");                           '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          cond = parse_expression;            '(Kwd ",");
          if_ = parse_list parse_statement;   '(Kwd ",");
          else_ = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: If"; 
      If(l, cond, if_, else_)
  | [< '(Kwd "Break");        '(Kwd "(");
          l = parse_loc;      '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Break"; 
      Break(l)
  | [< '(Kwd "Continue");     '(Kwd "(");
          l = parse_loc;      '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Continue"; 
      Continue(l)
  | [< '(Kwd "Return");                   '(Kwd "(");
          l = parse_loc;                  '(Kwd ",");
          e = parse_opt parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Return"; 
      Return(l, e)
  | [< '(Kwd "Throw");          '(Kwd "(");
          l = parse_loc;        '(Kwd ",");
          e = parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Throw"; 
      Throw(l, e)
  | [< '(Kwd "Assert");                    '(Kwd "(");
          l = parse_loc;                   '(Kwd ",");
          e1 = parse_expression;           '(Kwd ",");
          e2 = parse_opt parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_statement: Assert"; 
      Assert(l, e1, e2)
and parse_case = parser
  | [< '(Kwd "Case");                           '(Kwd "(");
          l = parse_loc;                        '(Kwd ",");
          matched = parse_opt parse_expression; '(Kwd ",");
          stmts = parse_list parse_statement;   '(Kwd ")");
    >] -> 
      debug_print "parse_case: Case"; 
      Case(l, matched, stmts)
and parse_catch_block = parser
  | [< '(Kwd "Catch");                        '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          excep = parse_var_decl;             '(Kwd ",");
          stmts = parse_list parse_statement; '(Kwd ")");
    >] -> 
      debug_print "parse_catch_block: Catch"; 
      Catch(l, excep, stmts)


(* expressions *)
and
  parse_expression = parser
  | [< '(Kwd "E_Identifier");    '(Kwd "(");
          id = parse_identifier; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: E_Identifier"; 
      E_Identifier(id)
  | [< '(Kwd "Access");          '(Kwd "(");
          l = parse_loc;         '(Kwd ",");
          e = parse_expression;  '(Kwd ",");
          id = parse_identifier; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Access"; 
      Access(l, e, id)
  | [< '(Kwd "Apply");                           '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          e = parse_expression;                  '(Kwd ",");
          args = parse_list parse_expression;    '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Apply"; 
      Apply(l, tparams, e, args)
  | [< '(Kwd "NewClass");                        '(Kwd "(");
          l = parse_loc;                         '(Kwd ",");
          tparams = parse_list parse_type_param; '(Kwd ",");
          clss = parse_ref_type;                 '(Kwd ",");
          args = parse_list parse_expression;    '(Kwd ")");
    >] -> 
      debug_print "parse_expression: NewClass"; 
      NewClass(l, tparams, clss, args)
  | [< '(Kwd "NewArray");                     '(Kwd "(");
          l = parse_loc;                      '(Kwd ",");
          typ = parse_type;                   '(Kwd ",");
          dims = parse_list parse_expression; '(Kwd ",");
          elem = parse_list parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: NewArray"; 
      NewArray(l, typ, dims, elem)
  | [< '(Kwd "Assign");                         '(Kwd "(");
          l = parse_loc;                        '(Kwd ",");
          op = parse_opt parse_bin_operator;    '(Kwd ",");
          lhs = parse_expression;               '(Kwd ",");
          rhs = parse_expression;               '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Assign"; 
      Assign(l, op, lhs, rhs)
  | [< '(Kwd "Unary");             '(Kwd "(");
          l = parse_loc;           '(Kwd ",");
          op = parse_uni_operator; '(Kwd ",");
          e = parse_expression;    '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Unary"; 
      Unary(l, op, e)
  | [< '(Kwd "Binary");            '(Kwd "(");
          l = parse_loc;           '(Kwd ",");
          op = parse_bin_operator; '(Kwd ",");
          lhs = parse_expression;  '(Kwd ",");
          rhs = parse_expression;  '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Binary"; 
      Binary(l, op, lhs, rhs)
  | [< '(Kwd "Ternary");             '(Kwd "(");
          l = parse_loc;             '(Kwd ",");
          cond = parse_expression;   '(Kwd ",");
          true_ = parse_expression;  '(Kwd ",");
          false_ = parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Ternary"; 
      Ternary(l, cond, true_, false_)
  | [< '(Kwd "ArrayAccess");         '(Kwd "(");
          l = parse_loc;             '(Kwd ",");
          array_ = parse_expression; '(Kwd ",");
          index = parse_expression;  '(Kwd ")");
    >] -> 
      debug_print "parse_expression: ArrayAccess"; 
      ArrayAccess(l, array_, index)
  | [< '(Kwd "Literal");        '(Kwd "(");
          l = parse_loc;        '(Kwd ",");
          typ = parse_type;     '(Kwd ",");
          value = parse_string; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: Literal"; 
      Literal(l, typ, value)
  | [< '(Kwd "TypeCast");       '(Kwd "(");
          l = parse_loc;        '(Kwd ",");
          typ = parse_type;     '(Kwd ",");
          e = parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: TypeCast"; 
      TypeCast(l, typ, e)
  | [< '(Kwd "TypeTest");       '(Kwd "(");
          l = parse_loc;        '(Kwd ",");
          typ = parse_type;     '(Kwd ",");
          e = parse_expression; '(Kwd ")");
    >] -> 
      debug_print "parse_expression: TypeTest"; 
      TypeTest(l, typ, e)
and
  parse_bin_operator = parser
  | [< '(Kwd "O_Plus") >]    -> debug_print ("parse_bin_operator: O_Plus");    O_Plus
  | [< '(Kwd "O_Min") >]     -> debug_print ("parse_bin_operator: O_Min");     O_Min
  | [< '(Kwd "O_Mul") >]     -> debug_print ("parse_bin_operator: O_Mul");     O_Mul
  | [< '(Kwd "O_Div") >]     -> debug_print ("parse_bin_operator: O_Div");     O_Div
  | [< '(Kwd "O_Mod") >]     -> debug_print ("parse_bin_operator: O_Mod");     O_Mod
  | [< '(Kwd "O_Or") >]      -> debug_print ("parse_bin_operator: O_Or");      O_Or
  | [< '(Kwd "O_And") >]     -> debug_print ("parse_bin_operator: O_And");     O_And
  | [< '(Kwd "O_Eq") >]      -> debug_print ("parse_bin_operator: O_Eq");      O_Eq
  | [< '(Kwd "O_NotEq") >]   -> debug_print ("parse_bin_operator: O_NotEq");   O_NotEq
  | [< '(Kwd "O_Lt") >]      -> debug_print ("parse_bin_operator: O_Lt");      O_Lt
  | [< '(Kwd "O_Gt") >]      -> debug_print ("parse_bin_operator: O_Gt");      O_Gt
  | [< '(Kwd "O_LtEq") >]    -> debug_print ("parse_bin_operator: O_LtEq");    O_LtEq
  | [< '(Kwd "O_GtEq") >]    -> debug_print ("parse_bin_operator: O_GtEq");    O_GtEq
  | [< '(Kwd "O_BitOr") >]   -> debug_print ("parse_bin_operator: O_BitOr");   O_BitOr
  | [< '(Kwd "O_BitXor") >]  -> debug_print ("parse_bin_operator: O_BitXor");  O_BitXor
  | [< '(Kwd "O_BitAnd") >]  -> debug_print ("parse_bin_operator: O_BitAnd");  O_BitAnd
  | [< '(Kwd "O_ShiftL") >]  -> debug_print ("parse_bin_operator: O_ShiftL");  O_ShiftL
  | [< '(Kwd "O_ShiftR") >]  -> debug_print ("parse_bin_operator: O_ShiftR");  O_ShiftR
  | [< '(Kwd "O_UShiftR") >] -> debug_print ("parse_bin_operator: O_UShiftR"); O_UShiftR
and
  parse_uni_operator = parser
  | [< '(Kwd "O_Pos") >]     -> debug_print ("parse_uni_operator: O_Pos");     O_Pos
  | [< '(Kwd "O_Neg") >]     -> debug_print ("parse_uni_operator: O_Neg");     O_Neg
  | [< '(Kwd "O_Not") >]     -> debug_print ("parse_uni_operator: O_Not");     O_Not
  | [< '(Kwd "O_Compl") >]   -> debug_print ("parse_uni_operator: O_Compl");   O_Compl
  | [< '(Kwd "O_PreInc") >]  -> debug_print ("parse_uni_operator: O_PreInc");  O_PreInc
  | [< '(Kwd "O_PreDec") >]  -> debug_print ("parse_uni_operator: O_PreDec");  O_PreDec
  | [< '(Kwd "O_PostInc") >] -> debug_print ("parse_uni_operator: O_PostInc"); O_PostInc
  | [< '(Kwd "O_PostDec") >] -> debug_print ("parse_uni_operator: O_PostDec"); O_PostDec
end
