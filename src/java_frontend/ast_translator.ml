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

open Lexer

exception AstTranslatorException of loc * string


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
  raise (AstTranslatorException(l, m))
let warning l m =
  let delim = "????????????????????????????????????????????????"in
  Printf.printf "%s\n%s\n%s\n" delim (m ^ " - " ^ (Lexer.string_of_loc l)) delim
  
(* ------------------------------------------------ *)
(* Parsing of annotations using the VeriFast parser *)
(* ------------------------------------------------ *)

let annotations : (string, string) Hashtbl.t ref = ref (Hashtbl.create 1)

(* this function creates a lexer for each of 
   the annotations and composes them before
   passing the resulting stream to the parser *)
let parse_pure_decls_core used_parser anns autogen =
  Parser.set_language Java;
  if (List.length anns < 1) then
    raise (Lexer.ParseException (dummy_loc, "Composing of lexers for parsing annotations failed (empty list of annotations)"));
  let (loc, token_stream) =
    let make_ann_lexer ann =
      match ann with
        GEN.Annotation(l, a) -> 
        let a = 
          if autogen then
            a
          else
            Hashtbl.find !annotations (Lexer.string_of_loc l) 
        in
        begin
          let (srcpos1, _) = l in
          let reportRange kind ((_, line1, col1), (_, line2, col2)) =
            ()  (* TODO implement *)
          in
          let reportShouldFail =
            fun _ -> () (* TODO implement *)
          in
          let annotChar =
            '@' (* TODO get correct value *)
          in
          let (loc, _, token_stream, _, _) =
            Lexer.make_lexer_core (Parser.common_keywords @ Parser.java_keywords) 
                                  Parser.ghost_keywords srcpos1 a reportRange
                                  false true true reportShouldFail annotChar
          in
          (loc, token_stream)
        end
    in
    let lexers = List.map make_ann_lexer anns in
    let index = ref 0 in
    let current_loc () =
      if (!index >= List.length lexers) then
        raise (Lexer.ParseException (dummy_loc, "Composing of lexers for parsing annotations failed (index past end of list)"))
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
    used_parser token_stream
  with
    Lexer.Stream.Error msg -> raise (Lexer.ParseException (loc(), msg))
  | Lexer.Stream.Failure -> raise (Lexer.ParseException (loc(), "Parse error"))

let parse_pure_decls anns autogen =
  let parser_pure_decls_eof = parser 
    [< ds = Parser.parse_decls VF.Java ~inGhostHeader:true;
      _ = Lexer.Stream.empty >] -> ds
  in
  parse_pure_decls_core parser_pure_decls_eof anns autogen

let parse_postcondition anns autogen =
  let parser_postcondition_eof = parser 
    [< '(_, Lexer.Kwd "ensures"); post = Parser.parse_pred; '(_, Lexer.Kwd ";"); 
       _ = Lexer.Stream.empty >] -> post
  in
  parse_pure_decls_core parser_postcondition_eof anns autogen

let parse_contract anns autogen =
  parse_pure_decls_core Parser.parse_spec anns autogen
  
let parse_instance_preds classname ann autogen =
  parse_pure_decls_core (Parser.parse_ghost_java_members classname) [ann] autogen

let parse_pure_statement l ann autogen =
  let parse_pure_statement_eof = parser
    [< s = Parser.parse_stmt0; _ = Lexer.Stream.empty >] -> PureStmt (l, s)
  in
  parse_pure_decls_core parse_pure_statement_eof [ann] autogen

let parse_loop_invar anns autogen =
  let parse_loop_invar_eof = parser 
    [<
      inv =
        Parser.opt
          begin parser
          | [< '(_, Lexer.Kwd "requires"); pre = Parser.parse_pred; '(_, Lexer.Kwd ";");
              '(_, Lexer.Kwd "ensures"); post = Parser.parse_pred; '(_, Lexer.Kwd ";") >] -> VF.LoopSpec (pre, post)
          | [< '(_, Lexer.Kwd "invariant"); p = Parser.parse_pred; '(_, Lexer.Kwd ";"); >] -> VF.LoopInv p
          end;
      dec = Parser.opt (parser [< '(_, Lexer.Kwd "decreases"); decr = Parser.parse_expr; '(_, Lexer.Kwd ";"); >] -> decr)
    >] -> (inv, dec)
  in
  parse_pure_decls_core parse_loop_invar_eof anns autogen

(* ------------------------------------------------ *)
(* Translation of Ast's                             *)
(* ------------------------------------------------ *)

let rec translate_ast package anns =
  annotations := anns;
  translate_package package

and translate_package package =
  debug_print_begin "translate_package";
  match package with
    GEN.Package(l, name, imprts, decls) ->
      let name'   = translate_name name in
      (* necessary to also import java.lang.* to find required definitions *)
      let imprts' = VF.Import(dummy_loc,"java.lang",None)::(List.map translate_import imprts) in
      let decls'  = List.flatten (List.map translate_package_decl decls) in
      debug_print_end ("translate_package: " ^ name');
      VF.PackageDecl(l, name', imprts', decls')

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

and translate_import imprt =
  debug_print_begin "translate_import";
  match imprt with
    GEN.Import(l, name, id) ->
      let name' = translate_name name in
      let id' = Misc.apply_option translate_identifier id in
      debug_print_end ("translate_import: " ^ name');
      VF.Import(l, name', id')

(* one 'decl' can result in multiple translated ones due to uninterpreted annotations *)
and translate_package_decl decl =
  debug_print_begin "translate_package_decl";
  let res =
    match decl with
      GEN.P_Annotation a -> 
        parse_pure_decls [a] false
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
        let fin' = translate_finality fin in
        let id' = GEN.string_of_identifier id in
        let (decls', meths') = translate_methods id' decls in
        let (decls', fields') = translate_fields decls' in
        let (decls', cons') = translate_constructors decls' in
        let extnds' =
          match extnds with
            Some x -> GEN.string_of_ref_type x
          | None -> "java.lang.Object"
        in
        let impls' = List.map GEN.string_of_ref_type impls in
        let (decls', preds') = translate_class_preds id' decls' in
        assert (decls' = []);
        (VF.Class(l, abs, fin', id', meths', fields', cons', extnds', impls', preds'), id')
    | GEN.Interface(l, anns, id, tparams, access, impls, decls) ->
        let id' = GEN.string_of_identifier id in
        let impls' = List.map GEN.string_of_ref_type impls in
        let (decls', fields') = translate_fields decls in
        let (decls', meths') = translate_methods id' decls' in
        let (decls', preds') = translate_class_preds id' decls' in
        assert (decls' = []);
        (VF.Interface(l, id', impls', fields', meths', preds'), id')
  in 
  debug_print_end ("translate_class_decl " ^ name');
  res

and translate_finality f =
  debug_print "translate_finality";
  match f with
    true -> VF.FinalClass
  | false -> VF.ExtensibleClass
  
and translate_visibility v =
  debug_print "translate_visibility";
  match v with
    GEN.PublicAccess -> VF.Public
  | GEN.PackageAccess -> VF.Package
  | _ -> VF.Private
  
and translate_visibility_ext prot v =
  debug_print "translate_visibility_ext";
  if prot then
    VF.Protected
  else
    translate_visibility v

and translate_binding stat =
  debug_print "translate_binding";
  if stat then
    VF.Static
  else
    VF.Instance

and translate_block l stmts =
  match stmts with
    Some stmts -> Some (List.map translate_statement stmts, l)
  | None -> None

and translate_class_decls_helper : 'a . (GEN.class_decl -> 'a list option) -> 
                                         GEN.class_decl list -> (GEN.class_decl list * 'a list) = 
  debug_print "translate_class_decls";
  fun translator decls ->
  begin
    match decls with
    | d::decls ->
      begin
        let (unmatched, matched) = translate_class_decls_helper translator decls in
        debug_print_begin "translate_class_decl";
        let res =
          match translator d with
          | Some d -> (unmatched, d @ matched)
          | None -> (d::unmatched, matched)
        in
        debug_print_end "translate_class_decl";
        res
      end
    | [] -> ([],[])
  end

and translate_methods cn decls = 
  debug_print "translate_methods";
  let translator decl =
    match decl with
    | GEN.C_Method m -> 
      begin
        match m with
          GEN.Method(l, anns, id, tparams, access, prot, abs, fin, stat, ret, params, throws, stmts) ->
            let ghost' = VF.Real in
            let ret' = 
              match ret with
                GEN.PrimType(GEN.VoidType _) -> None
              | _ -> Some (translate_type ret)
            in
            let id' = GEN.string_of_identifier id in
            let params' = 
              let params' = List.map translate_param params in
              if stat then
                params'
              else
                (* Adding the implicit this parameter as an explicit one *)
                (IdentTypeExpr (l, None, cn), "this")::params' 
            in
            let contr' = 
              let (pre,post) =
                if List.length anns = 0 then begin
                  let ann_pre = Annotation(l, "requires false; ") in
                  let ann_post = Annotation(l, "ensures true; ") in
                  parse_contract [ann_pre; ann_post] true
                end else
                  parse_contract anns false
              in
              let throws' = List.map translate_throws_clause throws in
              Some(pre, post, throws')
            in
            let stmts' = translate_block l stmts in
            let vis' = translate_visibility_ext prot access in
            let bind' = translate_binding stat in
            Some([VF.Meth(l, ghost', ret', id', params', contr', stmts', bind', vis', abs)])
        | _ -> None
      end
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_constructors decls = 
  debug_print "translate_constructors";
  let translator decl =
    match decl with
    | GEN.C_Method m -> 
      begin
        match m with
          GEN.Constructor(l, anns, id, tparams, access, prot, params, throws, stmts, autogen) ->
            let params' = List.map translate_param params in
            let contr' = 
              let (pre, post) =
                if autogen then begin
                  let ann_pre = Annotation(l, "requires true; ") in
                  let ann_post = Annotation(l, "ensures true; ") in
                  parse_contract [ann_pre; ann_post] true
                end else
                  parse_contract anns false
              in
              let throws' = List.map translate_throws_clause throws in
              Some(pre, post, throws')
            in
            let stmts' = translate_block l (Some(stmts)) in
            let vis' = translate_visibility_ext prot access in
            Some([VF.Cons(l, params', contr', stmts', vis')])
        | _ -> None
      end
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_param param =
  debug_print_begin "translate_param";
  let (res, id') =
    match param with
      GEN.Variable(l, id, _, _, _, _, typ, _)-> 
        let id' = translate_identifier id in
        let typ' = translate_type typ in
        ((typ', id'), id')
  in
  debug_print_end ("translate_param " ^ id');
  res

and translate_throws_clause (rtype, ann) =
  debug_print "translate_throws";
  let rtype' = translate_ref_type rtype in
  let post = parse_postcondition [ann] false in
  (rtype', post)

and translate_fields decls = 
  debug_print "translate_fields";
  let translator decl =
    match decl with
    | GEN.C_Variable m -> 
      begin
        match m with
          GEN.Variable(l, id, access, prot, fin, stat, typ, init) ->
            let ghost' = VF.Real in
            let typ' = translate_type typ in
            let id' = GEN.string_of_identifier id in
            let bind' = translate_binding stat in
            let vis' = translate_visibility_ext prot access in
            let init' = Misc.apply_option translate_expression init in
            Some([VF.Field(l, ghost', typ', id', bind', vis', fin, init')])
      end
    | _ -> None
  in 
  translate_class_decls_helper translator decls

and translate_class_preds classname decls = 
  debug_print "translate_preds";
  let translator decl =
    match decl with
    | GEN.C_Annotation a -> 
        Some(Parser.instance_preds (parse_instance_preds classname a false))
    | _ -> None
  in 
  translate_class_decls_helper translator decls
  
and translate_type (typ : GEN.type_) : VF.type_expr = 
  debug_print "translate_type";
  match typ with
    GEN.PrimType t -> translate_prim_type t
  | GEN.RefType t -> translate_ref_type t
  | GEN.ArrayType t -> VF.ArrayTypeExpr(Lexer.dummy_loc, translate_ref_type t)

and translate_prim_type typ =
  debug_print "translate_prim_type";
  match typ with
  | GEN.VoidType l -> VF.ManifestTypeExpr(l, VF.Void)
  | GEN.BoolType l -> VF.ManifestTypeExpr(l, VF.Bool)
  | GEN.CharType l -> VF.ManifestTypeExpr(l, VF.Char)
  (* TODO fix type here *)
  | GEN.ByteType l -> VF.ManifestTypeExpr(l, VF.ShortType)
  | GEN.ShortType l -> VF.ManifestTypeExpr(l, VF.ShortType)
  | GEN.IntType l -> VF.ManifestTypeExpr(l, VF.IntType)
  (* TODO fix type here *)
  | GEN.LongType l -> VF.ManifestTypeExpr(l, VF.IntType)
  (* TODO fix type here *)
  | GEN.FloatType l -> VF.ManifestTypeExpr(l, VF.RealType)
  (* TODO fix type here *)
  | GEN.DoubleType l -> VF.ManifestTypeExpr(l, VF.RealType)

and translate_ref_type typ = 
  debug_print "translate_ref_type";
  match typ with
  (* TODO check correctness + fix loc *)
  | GEN.SimpleRef(Name(l, ids)) ->
      VF.IdentTypeExpr(l, retrieve_package_name (Name(l, ids)), GEN.string_of_identifier (List.hd (List.rev ids)))
  | GEN.TypeApply(l, name, typs) -> 
      let typs' = List.map translate_ref_type typs in
      VF.ConstructedTypeExpr(l, GEN.string_of_name name, typs')
  (* TODO enhance support *)
  | GEN.WildCard(l, bound, kind) -> error l "Wildcards not supported yet"

and translate_statement stmt =
  debug_print "translate_statement";
  match stmt with
  | GEN.S_Annotation(Annotation(l, a)) ->
      parse_pure_statement l (Annotation(l, a)) false
  | GEN.S_Variable(Variable(l, id, access, _, fin, stat, typ, init)) ->
      let typ' = translate_type typ in
      let id' = translate_identifier id in
      let init' = Misc.apply_option translate_expression init in
      VF.DeclStmt (l, [(l, typ', id', init', ref false)])
  | GEN.S_Expression(e) ->
      begin
        match e with
        | GEN.Apply(l, tparams, GEN.E_Identifier(GEN.Identifier(l_id, "super")), exprs) ->
            let exprs' = List.map translate_expression exprs in
            VF.SuperConstructorCall(l, exprs')
        | _ -> 
            VF.ExprStmt (translate_expression e)
      end
  | GEN.Block(l, stmts) ->
      (* TODO: findout meaning of all arguments to this constructor*)
      VF.BlockStmt(l, [], List.map translate_statement stmts, dummy_loc, ref [])
  | GEN.Try(l, stmts, catchs) ->
      let stmts' = List.map translate_statement stmts in
      let catchs' = List.map translate_catch catchs in
      VF.TryCatch(l, stmts', catchs')
  | GEN.While(l, anns, expr, stmt) ->
      let expr' = translate_expression expr in
      let stmts' = List.map translate_statement stmt in
      let (inv, dec) = 
        if List.length anns = 0 then begin
          warning l ("While loop does not have a valid invariant");
          (None, None)
        end else
          parse_loop_invar anns false
      in
      VF.WhileStmt(l, expr', inv, dec, stmts')
  | GEN.DoWhile(l, anns, expr, stmt) ->
      let expr' = translate_expression expr in
      let stmts' = List.map translate_statement stmt in
      let (inv, dec) = 
        if List.length anns = 0 then begin
          warning l ("While loop does not have a valid invariant");
          (None, None)
        end else
          parse_loop_invar anns false
      in
      let body = VF.BlockStmt(l, [], stmts', dummy_loc, ref []) in
      let while_ = VF.WhileStmt(l, expr', inv, dec, stmts') in
      VF.BlockStmt(l, [], [body; while_], dummy_loc, ref [])
  | GEN.For(l, anns, init, expr, update, stmt) ->
      let (inv, dec) = 
        if List.length anns = 0 then begin
          warning l ("For loop does not have a valid invariant");
          (None, None)
        end else
          parse_loop_invar anns false
      in
      let init' = List.map translate_statement init in
      let expr' = translate_expression expr in
      let update' = List.map translate_statement update in
      let stmts' = List.map translate_statement stmt in
      VF.BlockStmt (l, [], init' @ [WhileStmt (l, expr', inv, dec, stmts' @ update')], l, ref [])
  | GEN.If(l, expr, stmt_true, stmt_false) ->
      let expr' = translate_expression expr in
      let stmt_true' =  [translate_statement stmt_true] in
      let stmt_false' = [translate_statement stmt_false] in
      VF.IfStmt(l, expr', stmt_true', stmt_false')
  | GEN.Return(l, expr) ->
      let expr' = Some(translate_expression expr) in
      VF.ReturnStmt(l, expr')
  | GEN.Throw(l, expr) ->
      let expr' = translate_expression expr in
      VF.Throw(l, expr')
  (* TODO: finish implementation *)
  | GEN.Foreach(l, _, _, _, _) -> error l "Foreach statements are not supported yet by the VeriFast ast" 
(*   | _ -> error dummy_loc "statement not supported yet" *)

and translate_catch catch =
  match catch with
    GEN.Catch(l, Variable(lv, id, _, _, _, _, typ, _), stmts) -> 
      let id' = translate_identifier id in
      let typ' = translate_type typ in
      let stmts' = List.map translate_statement stmts in
      (l, typ', id', stmts')

and translate_expression expr =
  debug_print "translate_expression";
  match expr with
    GEN.E_Identifier(Identifier(l, id)) -> 
      VF.Var(l, id, ref None)
  | GEN.Access(l, expr, id) ->
      let expr' = translate_expression expr in
      let id' = translate_identifier id in
      VF.Read(l, expr', id')
  | GEN.Apply(l, tparams, expr, exprs) ->
      if (List.length tparams <> 0) then
        error l "Generics should be erased before using this translator";
      let exprs' = List.map translate_expression exprs in
      let pats' = List.map (fun e -> VF.LitPat e) exprs' in
      begin
        match expr with
        | GEN.E_Identifier(GEN.Identifier(l_id, id)) -> 
            VF.CallExpr(l, id, [], [], pats', VF.Static)
        | GEN.Access(l_a, expr, Identifier(l_id, id)) ->
            let expr' = translate_expression expr in
            VF.CallExpr(l, id, [], [], (VF.LitPat expr')::pats', VF.Instance)
        | _ -> error l "Internal error of ast_translator";
      end
  | GEN.NewClass(l, tparams, typ, exprs) ->
      if (List.length tparams <> 0) then
        error l "Generics should be erased before using this translator";
      let typ' = GEN.string_of_ref_type typ in
      let exprs' = List.map translate_expression exprs in
      VF.NewObject(l, typ', exprs')
  | GEN.NewArray(l, typ, exprs) ->
      let typ' = translate_type typ in
      let exprs' = List.map translate_expression exprs in
      VF.NewArrayWithInitializer(l, typ', exprs')
  | GEN.Assign(l, op, expr_l, expr_r) ->
      let expr_l' = translate_expression expr_l in
      let expr_r' = translate_expression expr_r in
      begin
        match op with 
          Some op -> 
            let (_, op') = translate_bin_operator op in
            AssignOpExpr(l, expr_l', op', expr_r', false, ref None, ref None)
        | _ -> AssignExpr(l, expr_l', expr_r')
      end
  | GEN.Binary(l, op, expr_l, expr_r) ->
      let left = translate_expression expr_l in
      let right = translate_expression expr_r in
      let (rev, op') = translate_bin_operator op in
      let (expr_l', expr_r') =
        if rev then (right, left) else (left, right)
      in
      Operation(l, op', [expr_l'; expr_r'], ref None)
  | GEN.TypeCast(l, typ, expr) ->
      let typ' = translate_type typ in
      let expr' = translate_expression expr in
      VF.CastExpr(l, false, typ', expr')
  | GEN.Literal(l, typ, value) ->
      translate_literal l typ value 
  (* TODO: finish implementation *)
  | GEN.Unary(l, op, expr) -> 
      error l "unary operators not supported yet"
(*   | _ -> error dummy_loc "expression not supported yet" *)

and translate_bin_operator op =
  debug_print "operator";
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

and translate_literal l typ value =
  debug_print "translate_literal";
  match typ with
  | GEN.PrimType t ->
    begin
      match t with
        | GEN.VoidType(l) -> VF.Null(l)
        | GEN.BoolType(l) -> if value = "true" then VF.True(l) else VF.False(l)
        (* TODO: support all sizes of integers*)
        | GEN.CharType(l) -> VF.IntLit(l, Big_int.big_int_of_string value, ref None)
        | GEN.ByteType(l) -> VF.IntLit(l, Big_int.big_int_of_string value, ref None)
        | GEN.ShortType(l) -> VF.IntLit(l, Big_int.big_int_of_string value, ref None)
        | GEN.IntType(l) -> VF.IntLit(l, Big_int.big_int_of_string value, ref None)
        | GEN.LongType(l) -> VF.IntLit(l, Big_int.big_int_of_string value, ref None)
        | GEN.FloatType(l) -> error l "floats not supported yet"
        | GEN.DoubleType(l) -> error l "floats not supported yet"
  (*   | _ -> VF.StringLit(l, value) *)
    end
  | GEN.RefType t -> VF.Null(l)
  


































  