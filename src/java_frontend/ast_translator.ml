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

module VF = Ast
module GEN = General_ast

open VF
open GEN

open Ast
open Lexer
open Ast_writer

let indent = ref ""
let indent_string = "___"

let debug_print m = Printf.printf "<ast_translator> %s%s\n" !indent m 
let debug_print m = ()

let debug_print_begin m = 
  Printf.printf "<ast_translator> %s%s\n" !indent m;
  indent := !indent ^ indent_string
let debug_print_begin m = ()

let debug_print_end m = 
  indent := String.sub !indent 0 ((String.length !indent) - (String.length indent_string));
  Printf.printf "<ast_translator> %s%s\n" !indent m
let debug_print_end m = ()
  
let error l m =
  raise (ParseException(l, m))
  
(* ------------------------------------------------ *)
(* Translation of location                          *)
(* ------------------------------------------------ *)

let translate_location l =
  match l with 
  | GEN.NoSource -> dummy_loc
  | GEN.SourceLine(f, l, c1 ,c2) -> Lexed ((f, l, c1), (f, l, c2))
  | GEN.SourceLines(f, l1, c1, l2 ,c2) -> Lexed ((f, l1, c1), (f, l2, c2))

(* ------------------------------------------------ *)
(* Parsing of annotations using the VeriFast parser *)
(* ------------------------------------------------ *)

let annotations : (string, string list) Hashtbl.t ref = ref (Hashtbl.create 1)
let report_range : (Lexer.range_kind -> Ast.loc0 -> unit) ref = ref (fun _ _ -> ())
let report_should_fail : (Ast.loc0 -> unit) ref = ref (fun _ -> ())
let enforce_annotations : bool ref = ref false

module JavaParser = Parser.Parser (struct let language = Java let enforce_annotations = true let data_model = data_model_java end)

(* this function creates a lexer for each of 
   the annotations and composes them before
   passing the resulting stream to the parser *)
let parse_pure_decls_core loc used_parser anns lookup =
  if (List.length anns < 1) then
    error loc "Parsing failed due to missing annotations";
  let (loc, token_stream) =
    let make_ann_lexer ann =
      match ann with
        GEN.Annotation(l, a) -> 
        let a = 
          if lookup = false then
            a
          else
            try
              Misc.join_lines_fail (Hashtbl.find !annotations (General_ast.string_of_loc l))
            with 
              Not_found ->
                let message = "Annotation @ " ^ (General_ast.string_of_loc l) ^ "not found: \n" ^ a in
                error dummy_loc message;
            | Invalid_argument(_) -> 
                error loc "Parsing failed due to too big annotation";
        in
        let a = Str.global_replace (Str.regexp "\\\\\"") "\"" a in
        debug_print (Printf.sprintf "Handling annotation \n%s\n" a);
        begin
          let Lexed (srcpos1, _) = translate_location l in
          let annotChar = '*' in (*No nested annotations allowed, so no problem. JDK takes care of annotation char*)
          let (loc, _, token_stream, _, _) =
            Lexer.make_lexer_core (Parser.common_keywords @ Parser.java_keywords) 
                                  Parser.ghost_keywords srcpos1 a !report_range
                                  false true true !report_should_fail annotChar
          in
          (loc, token_stream)
        end
    in
    let lexers = List.map make_ann_lexer anns in
    let index = ref 0 in
    let current_loc () =
      if (!index >= List.length lexers) then
        error dummy_loc "Composing of lexers for parsing annotations failed (index past end of list)"
      else
        match List.nth lexers !index with (loc, _) -> loc ()
    in
    let rec next_token () =
      match List.nth lexers !index with (_, stream) ->
        match Lexer.Stream.peek stream with 
          Some (_, p) as t -> Lexer.Stream.junk stream; t
        | None ->
            if (!index < List.length lexers - 1) then
              (index := !index + 1; next_token ())
            else
              None
    in
    let stream = Stream.from (fun count -> next_token ()) in
    (current_loc, stream)
  in
  try
    used_parser (Parser.noop_preprocessor token_stream)
  with
    Lexer.Stream.Error msg -> error (Lexed (loc())) msg
  | Lexer.Stream.Failure -> error (Lexed (loc())) "Parse error"

let parse_ghost_import loc anns lookup =
  let parse_ghost_import_eof = parser 
    [< i = Parser.parse_import0; _ = Lexer.Stream.empty >] -> 
        match i with Import(l, Real, pn,el) -> Import(l, Ghost, pn,el)
  in
  parse_pure_decls_core loc parse_ghost_import_eof anns lookup

let parse_pure_decls loc anns lookup =
  let parser_pure_decls_eof = parser 
    [< ds = Parser.parse_decls VF.Java data_model_java ~inGhostHeader:true true;
      _ = Lexer.Stream.empty >] -> ds
  in
  parse_pure_decls_core loc parser_pure_decls_eof anns lookup

let parse_pure_decls_try anns lookup =
  try 
    parse_pure_decls dummy_loc anns lookup
  with parse_error -> []

let parse_postcondition loc anns lookup =
  let parser_postcondition_eof = parser 
    [< '(_, Lexer.Kwd "ensures"); post = JavaParser.parse_asn; '(_, Lexer.Kwd ";"); 
       _ = Lexer.Stream.empty >] -> post
  in
  parse_pure_decls_core loc parser_postcondition_eof anns lookup

let parse_contract loc anns lookup =
  let parse_contract_eof = parser 
    [< s = JavaParser.parse_spec; _ = Lexer.Stream.empty >] -> s
  in
  parse_pure_decls_core loc parse_contract_eof anns lookup
  
let parse_ghost_members loc classname ann =
  let rec parse_ghost_members_eof = parser
  | [< _ = Lexer.Stream.empty >] -> []
  | [< m = JavaParser.parse_ghost_java_member classname; mems = parse_ghost_members_eof >] -> m::mems
  in
  parse_pure_decls_core loc parse_ghost_members_eof [ann] false

let parse_pure_statement loc ann lookup =
  let parse_pure_statement_eof = parser
    [< s = JavaParser.parse_stmt0; _ = Lexer.Stream.empty >] -> PureStmt (loc, s)
  in
  parse_pure_decls_core loc parse_pure_statement_eof [ann] lookup

let parse_loop_invar loc anns lookup =
  let parse_loop_invar_eof = parser 
    [<
      inv =
        Parser.opt
          begin parser
          | [< '(_, Lexer.Kwd "requires"); pre = JavaParser.parse_asn; '(_, Lexer.Kwd ";");
              '(_, Lexer.Kwd "ensures"); post = JavaParser.parse_asn; '(_, Lexer.Kwd ";") >] -> VF.LoopSpec (pre, post)
          | [< '(_, Lexer.Kwd "invariant"); p = JavaParser.parse_asn; '(_, Lexer.Kwd ";"); >] -> VF.LoopInv p
          end;
      dec = Parser.opt (parser [< '(_, Lexer.Kwd "decreases"); decr = JavaParser.parse_expr; '(_, Lexer.Kwd ";"); >] -> decr)
    >] -> (inv, dec)
  in
  parse_pure_decls_core loc parse_loop_invar_eof anns lookup

(* ------------------------------------------------ *)
(* Translation of Ast's                             *)
(* ------------------------------------------------ *)

let rec translate_asts packages anns reportRange reportShouldFail enforce_annotations =
  List.map (fun x -> translate_ast x anns reportRange reportShouldFail enforce_annotations) packages

and translate_ast package anns report_range_ report_should_fail_ enforce_anns =
  annotations := anns;
  report_should_fail := report_should_fail_;
  enforce_annotations := enforce_anns;
  translate_package package 

and translate_package package =
  match package with
    GEN.Package(l, name, imprts, decls) ->
      let l' = translate_location l in
      let name'   = translate_name name in
      debug_print_begin ("translate_package " ^ name');
      (* necessary to also import java.lang.* to find required definitions *)
      let imprts' = VF.Import(dummy_loc,Real,"java.lang",None)::(List.map translate_import imprts) in
      let (decls', ghost_imports')  = translate_ghost_imports l' (decls, []) in
      let decls'  = List.flatten (List.map (translate_package_decl l') decls') in
      debug_print_end ("translate_package: " ^ name');
      VF.PackageDecl(l', name', imprts' @ ghost_imports', decls')

and translate_identifier id =
  debug_print_begin "translate_identifier";
  let res = GEN.string_of_identifier id in
  debug_print_end ("translate_identifier: " ^ res);
  res
  
and translate_name name =
  debug_print_begin "translate_name";
  let res = GEN.string_of_name name in
  debug_print_end ("translate_name" ^ res);
  res

and retrieve_package_name name =
  match name with 
    Name(_, ids) ->
    begin
      debug_print_begin "retrieve_package_name:";
      List.iter debug_print (List.map GEN.string_of_identifier ids);
      let ids = List.map GEN.string_of_identifier (List.rev (List.tl (List.rev ids))) in
      let res = String.concat "." ids in
      debug_print_end ("retrieve_package_name: " ^ res);
      if List.length ids = 0 then
        None
      else
        Some res
    end

and translate_ghost_imports loc (decls, imprts) =
  debug_print_begin "translate_ghost_import";
  match decls with
    (GEN.P_Annotation a)::decls' ->
    begin
      try
        let import =
          parse_ghost_import loc [a] true
        in
        debug_print_end "translate_ghost_import: Some";
        translate_ghost_imports loc (decls', import::imprts)
      with
        parse_error -> (debug_print_end "translate_ghost_import: None"; (decls, imprts))
    end
  | _ -> 
      (decls, imprts)

and translate_import imprt =
  debug_print_begin "translate_import";
  match imprt with
    GEN.Import(l, name, id) ->
      let name' = translate_name name in
      let id' = Misc.apply_option translate_identifier id in
      debug_print_end ("translate_import: " ^ name');
      VF.Import(translate_location l, Real, name', id')

(* one 'decl' can result in multiple translated ones due to uninterpreted annotations *)
and translate_package_decl loc decl =
  debug_print_begin "translate_package_decl";
  let res =
    match decl with
      GEN.P_Annotation a -> 
        parse_pure_decls loc [a] false
    | GEN.P_Class c -> 
        [translate_class_decl c]
  in
  debug_print_end "translate_package_decl";
  res
  
and translate_class_decl decl =
  debug_print_begin "translate_class_decl";
  let (res, name') = 
    match decl with
      GEN.Class(l, anns, id, tparams, access, abs, fin, stat, extnds, impls, decls) ->
        let l'= translate_location l in
        let abs' = translate_abstractness abs in
        let fin' = translate_class_finality fin in
        let id' = GEN.string_of_identifier id in
        debug_print ("class declaration " ^ id');
        let (decls', meths') = translate_methods id' decls in
        let (decls', static_blocks') = translate_static_blocks id' decls' in
        let (decls', fields') = translate_fields decls' in
        let (decls', cons') = translate_constructors decls' in
        let extnds' =
          match extnds with
            Some x -> GEN.string_of_ref_type x
          | None -> "java.lang.Object"
        in
        let impls' = List.map GEN.string_of_ref_type impls in
        let (decls', ghost_members') = translate_ghost_members l' id' decls' in
        let (ghost_fields', ghost_meths', ghost_preds') = split_ghost_members l ghost_members' in
        if (decls' <> []) then error l' "Not all declarations in class could be processed";
        (VF.Class(l', abs', fin', id', static_blocks' @ meths' @ ghost_meths', fields' @ ghost_fields', cons', extnds', impls', ghost_preds'), id')
    | GEN.Interface(l, anns, id, tparams, access, impls, decls) ->
        let l'= translate_location l in
        let id' = GEN.string_of_identifier id in
        debug_print ("interface declaration " ^ id');
        let impls' = List.map GEN.string_of_ref_type impls in
        let (decls', fields') = translate_fields decls in
        let (decls', meths') = translate_methods id' decls' in
        let (decls', ghost_members') = translate_ghost_members l' id' decls' in
        let (ghost_fields', ghost_meths', ghost_preds') = split_ghost_members l ghost_members' in
        if (decls' <> []) then error l' "Not all declarations in class could be processed";
        (VF.Interface(l', id', impls', fields' @ ghost_fields', meths' @ ghost_meths', ghost_preds'), id')
  in 
  debug_print_end ("translate_class_decl " ^ name');
  res

and split_ghost_members l ghost_members =
  let rec split_ghost_members_core all fields meths preds =
     match all with
     | FieldMember f::rest -> split_ghost_members_core rest (f @ fields) meths preds
     | MethMember m::rest -> split_ghost_members_core rest fields (m::meths) preds
     | PredMember p::rest -> split_ghost_members_core rest fields meths (p::preds)
     | [] -> (fields, meths, preds)
     | _ -> assert false
  in
  split_ghost_members_core ghost_members [] [] []

and translate_abstractness abs =
  debug_print "translate_abstractness";
  match abs with
  | GEN.Abstract -> true
  | GEN.NonAbstract -> false

and translate_class_finality fin =
  debug_print "translate_class_finality";
  match fin with
  | GEN.Final -> VF.FinalClass
  | GEN.NonFinal -> VF.ExtensibleClass

and translate_field_finality fin =
  debug_print "translate_field_finality";
  match fin with
  | GEN.Final -> true
  | GEN.NonFinal -> false

and translate_accessibility access =
  debug_print "translate_accessibility";
  match access with
  | GEN.PublicAccess -> VF.Public
  | GEN.PackageAccess -> VF.Package
  | GEN.ProtectedAccess -> VF.Protected
  | GEN.PrivateAccess -> VF.Private

and translate_staticness stat =
  debug_print "translate_staticness";
  match stat with
  | GEN.Static -> VF.Static
  | GEN.NonStatic -> VF.Instance

and next_body_rank =
  let counter = ref 0 in
  fun () -> incr counter; !counter

and translate_block l stmts =
  let l'= translate_location l in
  match stmts with
    Some stmts -> 
      begin
        let stmt' = translate_statements_as_block l' stmts in
        let stmts' =
          match stmt' with
          | VF.BlockStmt(l1, ds, VF.SuperConstructorCall(l2, exprs)::stms'', l3, _) -> 
            [VF.SuperConstructorCall(l2, exprs); 
             VF.BlockStmt(l1, ds, stms'', l3, ref [])]
          | _ -> [stmt']
        in 
        Some ((stmts', l'), next_body_rank ())
      end
  | None -> None

and translate_class_decls_helper : 'a . (GEN.class_decl -> 'a list option) ->
                                         GEN.class_decl list -> (GEN.class_decl list * 'a list) =
  fun translator decls ->
  begin
    match decls with
    | d::decls ->
      begin
        let (unmatched, matched) = translate_class_decls_helper translator decls in
        debug_print_begin "translate_class_decl some";
        let res =
          match translator d with
          | Some d -> (unmatched, d @ matched)
          | None -> (d::unmatched, matched)
        in
        debug_print_end "translate_class_decl";
        res
      end
    | [] -> debug_print "translate_class_decl some"; ([],[])
  end

and translate_static_blocks cn decls =
  let counter = ref 0 in
  debug_print "translate_static_blocks";
  let translator decl =
    match decl with
    | GEN.StaticBlock(l, stmts) ->
      begin
        let l' = translate_location l in
        let id' = cn ^ "_static_block_" ^ (string_of_int !counter) in
        counter := !counter + 1;
        let contr' = check_contract l [] [] Generated in
        let stmts' = translate_block l (Some stmts) in
        Some([VF.Meth(l', VF.Real, None, id', [], contr', stmts', VF.Static, VF.Private, false)])
      end
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and check_contract l anns throws generate =
  let l' = translate_location l in
  let anns' =
    if (List.length anns = 0) then
    (
      if (generate = Generated) then
        [Annotation(l, "requires true;"); Annotation(l, "ensures true;")]
      else if ((!enforce_annotations)) then
        error l' "Method must have a contract"
      else
        [Annotation(l, "requires false;"); Annotation(l, "ensures true;")]
    )
    else
      anns
  in
  let (pre', post', terminates') = parse_contract l' anns' false in
  let throws' = 
    List.map 
      (fun (t, c) -> 
        if (List.length anns = 0) then
        (
          let t' = translate_ref_type t in
          (t', ExprAsn(l', True(l')))
        )
        else
        (
          match translate_throws_clause l' (t, c) with 
            | (t', None) -> error l' "Throw clauses must have an ensures clause."
            | (t', Some(a)) -> (t', a)
        )
      )      
    throws
  in
  Some(pre', post', throws', terminates')

and translate_methods cn decls = 
  debug_print "translate_methods";
  let translator decl =
    match decl with
    | GEN.Method(l, anns, id, tparams, access, abs, fin, stat, ret, params, throws, stmts, autogen) ->
        let l' = translate_location l in
        let ghost' = VF.Real in
        let ret' = 
          match ret with
          | GEN.PrimType(GEN.VoidType _) -> None
          | GEN.RefType(GEN.SimpleRef(GEN.Name(_, [GEN.Identifier(_, "void")]))) -> None
          | _ -> Some (translate_type ret)
        in
        let id' = GEN.string_of_identifier id in
        debug_print ("method declaration " ^ id');
        let abs' = translate_abstractness abs in
        let access' = translate_accessibility access in
        let stat' = translate_staticness stat in
        let params' = 
          let params' = List.map translate_param params in
          match stat with
          | GEN.Static -> 
            params'
          | GEN.NonStatic ->
            (* Adding the implicit this parameter as an explicit one *)
            (IdentTypeExpr (translate_location l, None, cn), "this")::params'
        in
        let contr' = check_contract l anns throws autogen in
        let stmts' = translate_block l stmts in
        Some([VF.Meth(l', ghost', ret', id', params', contr', stmts', stat', access', abs')])
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_constructors decls = 
  debug_print "translate_constructors";
  (* Default constructors are handle by VeriFast *)
  let filter x =
    match x with GEN.Constructor(_, _, _, _, _, _, _, Generated) -> false | _ -> true
  in
  let decls = List.filter filter decls in
  let translator decl =
    match decl with
      | GEN.Constructor(l, anns, tparams, access, params, throws, stmts, autogen) ->
          let l' = translate_location l in
          let params' = List.map translate_param params in
          let contr' = check_contract l anns throws autogen in
          let stmts' = translate_block l stmts in
          let access' = translate_accessibility access in
          Some([VF.Cons(l', params', contr', stmts', access')])
      | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_param param =
  debug_print_begin "translate_param";
  let (res, id') =
    match param with
      GEN.Variable(l, id, typ, _)-> 
        let id' = translate_identifier id in
        let typ' = translate_type typ in
        ((typ', id'), id')
  in
  debug_print_end ("translate_param " ^ id');
  res

and translate_throws_clause loc (rtype, ann) =
  debug_print "translate_throws";
  let rtype' = translate_ref_type rtype in
  let post = 
    match ann with
      Some a -> Some(parse_postcondition loc [a] false)
    | None -> None
  in
  (rtype', post)

and translate_fields decls = 
  debug_print "translate_fields";
  let translator decl =
    match decl with
    | GEN.Field(l, id, access, fin, stat, typ, init, gen) ->
        let l' = translate_location l in
        let ghost' = VF.Real in
        let typ' = translate_type typ in
        let id' = GEN.string_of_identifier id in
        debug_print ("field declaration " ^ id');
        let stat' = translate_staticness stat in
        let access' = translate_accessibility access in
        let fin' = translate_field_finality fin in
        let init' = Misc.apply_option translate_expression init in
        Some([VF.Field(l', ghost', typ', id', stat', access', fin', init')])
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_ghost_members loc classname decls = 
  debug_print "translate_ghost_members";
  let translator decl =
    match decl with
    | GEN.C_Annotation a ->
        Some(parse_ghost_members loc classname a)
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_type (typ : GEN.type_) : VF.type_expr = 
  debug_print "translate_type";
  match typ with
    GEN.PrimType t -> translate_prim_type t
  | GEN.RefType t -> translate_ref_type t
  | GEN.ArrayType t -> VF.ArrayTypeExpr(dummy_loc, translate_type t)

and translate_prim_type typ =
  debug_print "translate_prim_type";
  match typ with
  | GEN.VoidType l -> VF.ManifestTypeExpr(translate_location l, VF.Void)
  | GEN.BoolType l -> VF.ManifestTypeExpr(translate_location l, VF.Bool)
  | GEN.CharType l -> VF.ManifestTypeExpr(translate_location l, VF.Int (VF.Unsigned, 1))
  | GEN.ByteType l -> VF.ManifestTypeExpr(translate_location l, VF.Int (VF.Signed, 0))
  | GEN.ShortType l -> VF.ManifestTypeExpr(translate_location l, VF.Int (VF.Signed, 1))
  | GEN.IntType l -> VF.ManifestTypeExpr(translate_location l, VF.Int (VF.Signed, 2))
  | GEN.LongType l -> VF.ManifestTypeExpr(translate_location l, VF.Int (VF.Signed, 3))
  | GEN.FloatType l -> VF.ManifestTypeExpr(translate_location l, VF.Float)
  | GEN.DoubleType l -> VF.ManifestTypeExpr(translate_location l, VF.Double)

and translate_ref_type typ = 
  debug_print "translate_ref_type";
  match typ with
  (* TODO check correctness + fix loc *)
  | GEN.SimpleRef(Name(l, ids)) ->
      let l' = translate_location l in
      let p' = retrieve_package_name (Name(l, ids)) in
      let id' = GEN.string_of_identifier (List.hd (List.rev ids)) in
      VF.IdentTypeExpr(l', p', id')
  | GEN.TypeApply(l, name, typs) -> 
      let l' = translate_location l in
      let typs' = List.map translate_ref_type typs in
      let name' = GEN.string_of_name name in
      VF.ConstructedTypeExpr(l', name', typs')
  (* TODO enhance support *)
  | GEN.WildCard(l, bound, kind) -> 
      let l' = translate_location l in
      error l' "Wildcards not supported yet"

and check_loop_invariant l' anns =
  if List.length anns = 0 then begin
    if !enforce_annotations then
      error l' ("While loop does not have a valid invariant")
    else
      (Some(LoopInv(ExprAsn(l', False(l')))), None)
  end else
    parse_loop_invar l' anns false

and add_casts_in_method_call arg_types exprs l =
  let rec iter (exprs, arg_types) =
    match (exprs, arg_types) with
    | (e::exprs, t::arg_types) ->
      let e = translate_expression e in
      let t = translate_type t in
      let e' =
        let l_e = expr_loc e in
        CastExpr(l_e, t, e)
      in
      e'::(iter(exprs, arg_types))
    | ([], []) -> []
    | _ ->  error l "Internal error while translating method application"
  in
  iter (exprs, arg_types) 

and translate_statement stmt =
  debug_print "translate_statement";
  match stmt with
  | GEN.S_Annotation(Annotation(l, a)) ->
      let l' = translate_location l in
      parse_pure_statement l' (Annotation(l, a)) false
  | GEN.S_Variable(Variable(l, id, typ, init)) ->
      let l' = translate_location l in
      let typ' = translate_type typ in
      let id' = translate_identifier id in
      let init' = Misc.apply_option translate_expression init in
      VF.DeclStmt (l', [(l', typ', id', init', (ref false, ref None))])
  | GEN.S_Expression(e) ->
      begin
        match e with
        | GEN.Apply(l, tparams, GEN.E_Identifier(GEN.Identifier(l_id, "super")), arg_types, exprs) ->
            let l' = translate_location l in
            let exprs' = add_casts_in_method_call arg_types exprs l' in
            VF.SuperConstructorCall(l', exprs')
        | _ -> 
            VF.ExprStmt (translate_expression e)
      end
  | GEN.Block(l, stmts) ->
      let l' = translate_location l in 
      translate_statements_as_block l' stmts
  | GEN.Try(l, stmts, catchs) ->
      let l' = translate_location l in
      let stmt' = translate_statements_as_block l' stmts in
      let catchs' = List.map translate_catch catchs in
      VF.TryCatch(l', [stmt'], catchs')
  | GEN.While(l, anns, expr, stmts) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      let stmt' = translate_statements_as_block l' stmts in
      let (inv, dec) = check_loop_invariant l' anns in
      VF.WhileStmt(l', expr', inv, dec, [stmt'], [])
  | GEN.DoWhile(l, anns, expr, stmts) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      let (inv, dec) = check_loop_invariant l' anns in
      let body = translate_statements_as_block l' stmts in
      let while_ = VF.WhileStmt(l', expr', inv, dec, [body], []) in
      VF.BlockStmt(l', [], [body; while_], dummy_loc, ref [])
  | GEN.For(l, anns, init, expr, update, stmts) ->
      let l' = translate_location l in
      let (inv, dec) = check_loop_invariant l' anns in
      let init' = List.map translate_statement init in
      let expr' = translate_expression expr in
      let update' = List.map translate_statement update in
      let stmt' = translate_statements_as_block l' stmts in
      VF.BlockStmt (l', [], init' @ [WhileStmt (l', expr', inv, dec, [stmt'], update')], l', ref [])
  | GEN.If(l, expr, stmts_true, stmts_false) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      let stmt_true' = translate_statements_as_block l' stmts_true in
      let stmt_false' = translate_statements_as_block l' stmts_false in
      VF.IfStmt(l', expr', [stmt_true'], [stmt_false'])
  | GEN.Return(l, expr) ->
      let l' = translate_location l in
      let expr' = Misc.apply_option translate_expression expr in
      VF.ReturnStmt(l', expr')
  | GEN.Throw(l, expr) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      VF.Throw(l', expr')
  | GEN.Switch(l, sel, cases, default) ->
      let l' = translate_location l in
      let sel' = translate_expression sel in
      let cases' = 
        let cases' = List.map translate_switch_case cases in
        match default with
          Some(default) -> (translate_switch_case default)::cases'
        | None -> cases'
      in
      VF.SwitchStmt(l', sel', cases')
  | GEN.Break(l) ->
      let l' = translate_location l in
      VF.Break(l')
  | GEN.Assert(l, expr, message) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      VF.Assert(l', VF.ExprAsn(l', expr'))
  | GEN.Continue(l) -> 
      let l' = translate_location l in
      error l' "Continue statements are not supported yet by VeriFast"
  | GEN.Labeled(l, _, _) -> 
      let l' = translate_location l in
      error l' "Labeled statements are not supported yet by VeriFast"
  | GEN.Foreach(l, _, _, _, _) -> 
      let l' = translate_location l in
      error l' "Internal error: Foreach statements are not supported by the VeriFast ast"

and translate_statements_as_block l stmts =
  let rec iter deps stmts =
    match (stmts) with
    | GEN.S_Annotation(a)::rest ->
      let ds = parse_pure_decls_try [a] false in
      if (ds <> []) then
        iter (ds @ deps) rest
      else
        (deps, stmts)
    | _ -> (deps, stmts)
  in
  let (deps, stmts) = iter [] stmts in
  let stmts' = List.map translate_statement stmts in
  VF.BlockStmt(l, deps, stmts', l, ref [])

and translate_catch catch =
  match catch with
    GEN.Catch(l, Variable(lv, id, typ, _), stmts) -> 
      let l' = translate_location l in
      let id' = translate_identifier id in
      let typ' = translate_type typ in
      let stmts' = List.map translate_statement stmts in
      (l', typ', id', stmts')

and translate_switch_case case =
  match case with
    GEN.Case(l, sel, stmts) ->
      let l' = translate_location l in
      let stmts' = List.map translate_statement stmts in
      match sel with
        Some(sel) -> 
          let sel' = translate_expression sel in
          SwitchStmtClause(l', sel', stmts')
      | None -> 
          SwitchStmtDefaultClause(l', stmts')

and translate_expression expr =
  debug_print "translate_expression";
  match expr with
    GEN.E_Identifier(Identifier(l, id)) -> 
      let l' = translate_location l in
      VF.Var(l', id)
  | GEN.Access(l, expr, id) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      let id' = translate_identifier id in
      VF.Read(l', expr', id')
  | GEN.Apply(l, tparams, expr, arg_types, exprs) ->
      let l' = translate_location l in
      if (List.length tparams <> 0) then
        error l' "Generics should be erased before using this translator";
      let exprs' = add_casts_in_method_call arg_types exprs l' in
      let pats' = List.map (fun e -> VF.LitPat e) exprs' in
      begin
        match expr with
        | GEN.E_Identifier(GEN.Identifier(l_id, id)) -> 
            let l' = translate_location l in
            VF.CallExpr(l', id, [], [], pats', VF.Static)
        | GEN.Access(l_a, expr, Identifier(l_id, id)) ->
            let l' = translate_location l in
            let expr' = translate_expression expr in
            begin
              match expr' with
              | VF.Var(_, "super") ->    
                  SuperMethodCall (l', id, exprs')     
              | _ -> VF.CallExpr(l', id, [], [], (VF.LitPat expr')::pats', VF.Instance)
            end
        | _ -> error l' "Internal error of ast_translator";
      end
  | GEN.NewClass(l, tparams, typ, exprs) ->
      let l' = translate_location l in
      if (List.length tparams <> 0) then
        error l' "Generics should be erased before using this translator";
      let typ' = GEN.string_of_ref_type typ in
      let exprs' = List.map translate_expression exprs in
      VF.NewObject(l', typ', exprs')
  | GEN.NewArray(l, typ, dims, exprs) ->
      let l' = translate_location l in
      let typ' = translate_type typ in
      let dims' = List.map translate_expression dims in
      let exprs' = List.map translate_expression exprs in
      if (List.length dims > 1) then
        error l' "Multiple dimensions for arrays creation not supported yet";
      if (List.length dims = 1) then
        VF.NewArray(l', typ', List.hd dims') 
      else
        VF.NewArrayWithInitializer(l', typ', exprs')
  | GEN.Assign(l, op, expr_l, expr_r) ->
      let l' = translate_location l in
      let expr_l' = translate_expression expr_l in
      let expr_r' = translate_expression expr_r in
      begin
        match op with 
          Some op -> 
            let (_, op') = translate_bin_operator op l' in
            AssignOpExpr(l', expr_l', op', expr_r', false)
        | _ -> AssignExpr(l', expr_l', expr_r')
      end
  | GEN.Unary(l, op, expr) -> 
      let l' = translate_location l in
      let expr' = translate_expression expr in
      translate_uni_operator op l' expr'
  | GEN.Binary(l, op, expr_l, expr_r) ->
      let l' = translate_location l in
      let left = translate_expression expr_l in
      let right = translate_expression expr_r in
      let (rev, op') = translate_bin_operator op l' in
      let (expr_l', expr_r') =
        if rev then (right, left) else (left, right)
      in
      VF.Operation(l', op', [expr_l'; expr_r'])
  | GEN.Ternary(l, expr1, expr2, expr3) ->
      let l' = translate_location l in
      let expr1' = translate_expression expr1 in
      let expr2' = translate_expression expr2 in
      let expr3' = translate_expression expr3 in
      VF.IfExpr(l', expr1', expr2', expr3')
  | GEN.TypeTest(l, type_expr, expr) ->
      let l' = translate_location l in
      let expr' = translate_expression expr in
      let type_expr' = translate_type type_expr in
      VF.InstanceOfExpr(l', expr', type_expr')
  | GEN.TypeCast(l, typ, expr) ->
      let l' = translate_location l in
      let typ' = translate_type typ in
      let expr' = translate_expression expr in
      VF.CastExpr(l', typ', expr')
  | GEN.Literal(l, typ, value) ->
      translate_literal l typ value 
  | GEN.ArrayAccess(l, expr1, expr2) ->
      let l' = translate_location l in
      let expr1' = translate_expression expr1 in
      let expr2' = translate_expression expr2 in
      VF.ReadArray(l', expr1', expr2')

and translate_bin_operator op l =
  debug_print "bin_operator";
  match op with
  | GEN.O_Plus   -> (false, VF.Add)
  | GEN.O_Min    -> (false, VF.Sub)
  | GEN.O_Mul    -> (false, VF.Mul)
  | GEN.O_Div    -> (false, VF.Div)
  | GEN.O_Mod    -> (false, VF.Mod)
  | GEN.O_Or     -> (false, VF.Or)
  | GEN.O_And    -> (false, VF.And)
  | GEN.O_Eq     -> (false, VF.Eq)
  | GEN.O_NotEq  -> (false, VF.Neq)
  | GEN.O_Lt     -> (false, VF.Lt)
  | GEN.O_Gt     -> (true, VF.Lt)
  | GEN.O_LtEq   -> (false, VF.Le)
  | GEN.O_GtEq   -> (true, VF.Le)
  | GEN.O_BitOr  -> (false, VF.BitOr)
  | GEN.O_BitXor -> (false, VF.BitXor)
  | GEN.O_BitAnd -> (false, VF.BitAnd)
  | GEN.O_ShiftL -> (false, VF.ShiftLeft);
  | GEN.O_ShiftR -> (false, VF.ShiftRight);
  | GEN.O_UShiftR-> error l "Binary operator >>> not supported yet";

and translate_uni_operator op l expr =
  debug_print "uni_operator";
  let intlit n = VF.IntLit(l, Big_int.big_int_of_int n, true, false, NoLSuffix) in
  match op with
  | GEN.O_Not     -> VF.Operation(l, VF.Eq, [VF.False(l); expr])
  | GEN.O_Pos     -> expr
  | GEN.O_Neg     -> VF.Operation(l, VF.Sub, [intlit 0; expr])
  | GEN.O_PreInc  -> VF.AssignOpExpr(l, expr, Add, intlit 1, false)
  | GEN.O_PreDec  -> VF.AssignOpExpr(l, expr, Sub, intlit 1, false)
  | GEN.O_PostInc -> VF.AssignOpExpr(l, expr, Add, intlit 1, true)
  | GEN.O_PostDec -> VF.AssignOpExpr(l, expr, Sub, intlit 1, true)
  | GEN.O_Compl   -> VF.Operation(l, VF.BitNot, [expr])

and translate_literal l typ value =
  debug_print "translate_literal";
  match typ with
  | GEN.PrimType t ->
    begin
      match t with
        | GEN.VoidType(l) -> 
            let l' = translate_location l in
            VF.Null(l')
        | GEN.BoolType(l) -> 
            let l' = translate_location l in
            if value = "true" then VF.True(l') else VF.False(l')

        (* TODO: support all sizes of integers*)
        | GEN.CharType(l) ->
            let l' = translate_location l in
            VF.IntLit(l', Big_int.big_int_of_string value, true, false, NoLSuffix)
        | GEN.ByteType(l) ->
            let l' = translate_location l in
            VF.IntLit(l', Big_int.big_int_of_string value, true, false, NoLSuffix)
        | GEN.ShortType(l) ->
            let l' = translate_location l in
            VF.IntLit(l', Big_int.big_int_of_string value, true, false, NoLSuffix)
        | GEN.IntType(l) ->
            let l' = translate_location l in
            VF.IntLit(l', Big_int.big_int_of_string value, true, false, NoLSuffix)
        | GEN.LongType(l) ->
            let l' = translate_location l in
            VF.IntLit(l', Big_int.big_int_of_string value, true, false, LSuffix)
        | GEN.FloatType(l) ->
            let l' = translate_location l in
            error l' "floats not supported yet"
        | GEN.DoubleType(l) ->
            let l' = translate_location l in
            error l' "floats not supported yet"
    end
  | GEN.RefType t ->
      let l' = translate_location l in
      match t with
      | SimpleRef(Name(_, [Identifier(_, "java"); Identifier(_, "lang"); Identifier(_, "String")])) -> VF.StringLit(l', value)
      | _ -> VF.Null(l')
      
  


































  
