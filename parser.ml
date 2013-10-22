open Big_int
open Num
open Util
open Stats
open Lexer
open Ast

(* Region: the parser *)

let common_keywords = [
  "switch"; "case"; ":"; "return"; "for";
  "void"; "if"; "else"; "while"; "!="; "<"; ">"; "<="; ">="; "&&"; "++"; "--"; "+="; "-="; "*="; "/="; "&="; "|="; "^="; "%="; "<<="; ">>="; ">>>=";
  "||"; "!"; "."; "["; "]"; "{"; "break"; "default";
  "}"; ";"; "int"; "true"; "false"; "("; ")"; ","; "="; "|"; "+"; "-"; "=="; "?"; "%"; 
(* Note: it's important for soundness that currentCodeFractions, currentThread, and varargs be considered keywords both inside and outside of annotations. *)
  "*"; "/"; "&"; "^"; "~"; "assert"; "currentCodeFraction"; "currentThread"; "varargs"; "short"; ">>"; "<<";
  "truncating"; "typedef"; "do";
  "->" (* Used for inductive value field access (e.g. "my_ind_value->my_param_name") in ghostcode, and struct field access in C and C-ghostcode. *)
]

let ghost_keywords = [
  "predicate"; "requires"; "|->"; "&*&"; "inductive"; "fixpoint";
  "ensures"; "close"; "lemma"; "open"; "emp"; "invariant"; "lemma_auto";
  "_"; "@*/"; "predicate_family"; "predicate_family_instance"; "predicate_ctor"; "leak"; "@";
  "box_class"; "action"; "handle_predicate"; "preserved_by"; "consuming_box_predicate"; "consuming_handle_predicate"; "perform_action"; "nonghost_callers_only";
  "create_box"; "above"; "below"; "and_handle"; "and_fresh_handle"; "create_handle"; "create_fresh_handle"; "dispose_box"; "produce_lemma_function_pointer_chunk"; "produce_function_pointer_chunk";
  "producing_box_predicate"; "producing_handle_predicate"; "producing_fresh_handle_predicate"; "box"; "handle"; "any"; "real"; "split_fraction"; "by"; "merge_fractions";
  "unloadable_module"; "decreases"; "load_plugin"; "forall_"; "import_module"; "require_module"; ".."; "extends"; "permbased"
]

let c_keywords = [
  "struct"; "bool"; "char"; "sizeof"; "#"; "include"; "ifndef";
  "define"; "endif"; "&"; "goto"; "uintptr_t"; "INT_MIN"; "INT_MAX";
  "UINTPTR_MAX"; "enum"; "static"; "signed"; "unsigned"; "long";
  "const"; "volatile"; "register"; "ifdef"; "elif"; "undef";
  "USHRT_MAX"; "UINT_MAX"; "UCHAR_MAX"; "..."
]

let java_keywords = [
  "public"; "char"; "private"; "protected"; "class"; "static"; "boolean"; "new"; "null"; "interface"; "implements"; "package"; "import";
  "throw"; "try"; "catch"; "throws"; "byte"; "final"; "extends"; "instanceof"; "super"; "abstract"
]

exception StaticError of loc * string * string option

let static_error l msg url = raise (StaticError (l, msg, url))

exception CompilationError of string

let file_type path=
  begin
  if Filename.check_suffix (Filename.basename path) ".c" then CLang
  else if Filename.check_suffix (Filename.basename path) ".jarsrc" then Java
  else if Filename.check_suffix (Filename.basename path) ".jarspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".java" then Java
  else if Filename.check_suffix (Filename.basename path) ".javaspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".scala" then Java
  else if Filename.check_suffix (Filename.basename path) ".h" then CLang
  else raise (CompilationError ("unknown extension: " ^ (Filename.basename path)))
  end
let opt p = parser [< v = p >] -> Some v | [< >] -> None
let rec comma_rep p = parser [< '(_, Kwd ","); v = p; vs = comma_rep p >] -> v::vs | [< >] -> []
let rep_comma p = parser [< v = p; vs = comma_rep p >] -> v::vs | [< >] -> []
let rec rep p = parser [< v = p; vs = rep p >] -> v::vs | [< >] -> []
let parse_angle_brackets (_, sp) p =
  parser [< '((sp', _), Kwd "<") when sp = sp'; v = p; '(_, Kwd ">") >] -> v

(* Does a two-token lookahead.
   Succeeds if it sees a /*@ followed by something that matches [p].
   Fails if it does not see /*@ or if [p] fails.
   Throws Stream.Error if [p] does. *)
let peek_in_ghost_range p stream =
  match Stream.peek stream with
    Some (_, Kwd "/*@") as tok ->
    Stream.junk stream;
    begin
      try
        p stream
      with
        Stream.Failure as e -> Stream.push tok stream; raise e
    end
  | _ -> raise Stream.Failure

type spec_clause = (* ?spec_clause *)
  NonghostCallersOnlyClause
| FuncTypeClause of string * type_expr list * (loc * string) list
| RequiresClause of asn
| EnsuresClause of asn

(* A toy Scala parser. *)
module Scala = struct

  let keywords = [
    "def"; "var"; "class"; "object"; "."; "new"; "null"; "package"; "import";
    "+"; "="; "("; ")"; ":"; "{"; "}"; "["; "]"; "/*@"; "@*/"; "=="; "="; ";"; "true"; "false"; "assert"
  ]

  let rec
    parse_decl = parser
      [< '(l, Kwd "object"); '(_, Ident cn); '(_, Kwd "{"); ms = rep parse_method; '(_, Kwd "}") >] ->
      Class (l, false, FinalClass, cn, ms, [], [], "Object", [], [])
  and
    parse_method = parser
      [< '(l, Kwd "def"); '(_, Ident mn); ps = parse_paramlist; t = parse_type_ann; co = parse_contract; '(_, Kwd "=");'(_, Kwd "{"); ss = rep parse_stmt; '(closeBraceLoc, Kwd "}")>] ->
      let rt = match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t in
      Meth (l, Real, rt, mn, ps, Some co,Some (ss, closeBraceLoc), Static, Public, false)
  and
    parse_paramlist = parser
      [< '(_, Kwd "("); ps = rep_comma parse_param; '(_, Kwd ")") >] -> ps
  and
    parse_param = parser
      [< '(_, Ident x); t = parse_type_ann >] -> (t, x)
  and
    parse_type_ann: (loc * token) Stream.t -> type_expr = parser
      [< '(_, Kwd ":"); t = parse_type >] -> t
  and
    parse_type = parser
      [< '(l, Ident tn); targs = parse_targlist >] ->
      begin
        match (tn, targs) with
          ("Unit", []) -> ManifestTypeExpr (l, Void)
        | ("Int", []) -> ManifestTypeExpr (l, IntType)
        | ("Array", [t]) -> ArrayTypeExpr (l, t)
        | (_, []) -> IdentTypeExpr (l, None, tn)
        | _ -> raise (ParseException (l, "Type arguments are not supported."))
      end
  and
    parse_targlist = parser
      [< '(_, Kwd "["); ts = rep_comma parse_type; '(_, Kwd "]") >] -> ts
    | [< >] -> []
  and
    parse_contract = parser
      [< '(_, Kwd "/*@"); '(_, Kwd "requires"); pre = parse_asn; '(_, Kwd "@*/");
         '(_, Kwd "/*@"); '(_, Kwd "ensures"); post = parse_asn; '(_, Kwd "@*/") >] -> (pre, post, [])
  and
    parse_asn = parser
      [< '(_, Kwd "("); a = parse_asn; '(_, Kwd ")") >] -> a
    | [< e = parse_expr >] -> ExprAsn (expr_loc e, e)
  and
    parse_primary_expr = parser
      [< '(l, Kwd "true") >] -> True l
    | [< '(l, Kwd "false") >] -> False l
    | [< '(l, Int n) >] -> IntLit (l, n, ref None)
    | [< '(l, Ident x) >] -> Var (l, x, ref None)
  and
    parse_add_expr = parser
      [< e0 = parse_primary_expr; e = parse_add_expr_rest e0 >] -> e
  and
    parse_add_expr_rest e0 = parser
      [< '(l, Kwd "+"); e1 = parse_primary_expr; e = parse_add_expr_rest (Operation (l, Add, [e0; e1], ref None)) >] -> e
    | [< >] -> e0
  and
    parse_rel_expr = parser
      [< e0 = parse_add_expr; e = parse_rel_expr_rest e0 >] -> e
  and
    parse_rel_expr_rest e0 = parser
      [< '(l, Kwd "=="); e1 = parse_add_expr; e = parse_rel_expr_rest (Operation (l, Eq, [e0; e1], ref None)) >] -> e
    | [< >] -> e0
  and
    parse_expr stream = parse_rel_expr stream
  and
    parse_stmt = parser
      [< '(l, Kwd "var"); '(_, Ident x); t = parse_type_ann; '(_, Kwd "="); e = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, [l, t, x, Some(e), ref false])
    | [< '(l, Kwd "assert"); a = parse_asn; '(_, Kwd ";") >] -> Assert (l, a)

end

(* The C/Java parser.
   The difference is in the scanner: when parsing a C file, the scanner treats "class" like an identifier, not a keyword.
   And Kwd "class" does not match Ident "class".
   *)

type modifier = StaticModifier | FinalModifier | AbstractModifier | VisibilityModifier of visibility

(* 
   To make parsing functions accessible from elsewhere, 
   without adding the argument 'language' to every function.
   TODO: find a better solution
*)
let language = ref CLang
let set_language lang =
  language := lang

let rec parse_decls lang ?inGhostHeader =
  set_language lang;
  if match inGhostHeader with None -> false | Some b -> b then
    parse_pure_decls
  else
    parse_decls_core
and
  parse_decls_core = parser
  [< '((p1, _), Kwd "/*@"); ds = parse_pure_decls; '((_, p2), Kwd "@*/"); ds' = parse_decls_core >] -> ds @ ds'
| [< _ = opt (parser [< '(_, Kwd "public") >] -> ());
     abstract = (parser [< '(_, Kwd "abstract") >] -> true | [< >] -> false); 
     final = (parser [< '(_, Kwd "final") >] -> FinalClass | [< >] -> ExtensibleClass);
     ds = begin parser
       [< '(l, Kwd "class"); '(_, Ident s); super = parse_super_class; il = parse_interfaces; mem = parse_java_members s; ds = parse_decls_core >]
       -> Class (l, abstract, final, s, methods s mem, fields mem, constr mem, super, il, instance_preds mem)::ds
     | [< '(l, Kwd "interface"); '(_, Ident cn); il = parse_extended_interfaces;  mem = parse_java_members cn; ds = parse_decls_core >]
       -> Interface (l, cn, il, fields mem, methods cn mem, instance_preds mem)::ds
     | [< d = parse_decl; ds = parse_decls_core >] -> d@ds
     | [< >] -> []
     end
  >] -> ds
and parse_qualified_type_rest = parser
  [< '(_, Kwd "."); '(_, Ident s); rest = parse_qualified_type_rest >] -> "." ^ s ^ rest
| [<>] -> ""
and parse_qualified_type = parser
  [<'(_, Ident s); rest = parse_qualified_type_rest >] -> s ^ rest
and
  parse_super_class= parser
    [<'(_, Kwd "extends"); s = parse_qualified_type >] -> s 
  | [<>] -> "java.lang.Object"
and
  parse_interfaces= parser
  [< '(_, Kwd "implements"); is = rep_comma (parser 
    [< i = parse_qualified_type; e=parser
      [<>]->(i)>] -> e); '(_, Kwd "{") >] -> is
| [<'(_, Kwd "{")>]-> []
and
  parse_extended_interfaces= parser
  [< '(_, Kwd "extends"); is = rep_comma (parser 
    [< i = parse_qualified_type; e=parser
      [<>]->(i)>] -> e); '(_, Kwd "{") >] -> is
| [<'(_, Kwd "{")>]-> []
and
  methods cn m=
  match m with
    MethMember (Meth (l, gh, t, n, ps, co, ss,s,v,abstract))::ms -> Meth (l, gh, t, n, ps, co, ss,s,v,abstract)::(methods cn ms)
    |_::ms -> methods cn ms
    | []->[]
and
  fields m=
  match m with
    FieldMember fs::ms -> fs @ (fields ms)
    |_::ms -> fields ms
    | []->[]
and
  constr m=
  match m with
    ConsMember(Cons(l,ps,co,ss,v))::ms -> Cons(l,ps,co,ss,v)::(constr ms)
    |_::ms -> constr ms
    | []->[]
and
  instance_preds mems = flatmap (function PredMember p -> [p] | _ -> []) mems
and
  parse_visibility = parser
  [<'(_, Kwd "public")>] -> Public
| [<'(_, Kwd "private")>] -> Private
| [<'(_, Kwd "protected")>] -> Protected
| [<>] -> Package
and
  parse_java_members cn= parser
  [<'(_, Kwd "}")>] -> []
| [< '(_, Kwd "/*@"); mems1 = parse_ghost_java_members cn; mems2 = parse_java_members cn >] -> mems1 @ mems2
| [< m=parse_java_member cn;mr=parse_java_members cn>] -> m::mr
and
  parse_ghost_java_members cn = parser
  [< '(_, Kwd "@*/") >] -> []
| [< vis = parse_visibility; m = begin parser
       [< '(l, Kwd "predicate"); '(_, Ident g); ps = parse_paramlist;
          body = begin parser
            [< '(_, Kwd "="); p = parse_pred >] -> Some p
          | [< >] -> None
          end;
          '(_, Kwd ";") >] -> PredMember (InstancePredDecl (l, g, ps, body))
     | [< '(l, Kwd "lemma"); t = parse_return_type; '(l, Ident x); (ps, co, ss) = parse_method_rest >] ->
       let ps = (IdentTypeExpr (l, None, cn), "this")::ps in
       MethMember (Meth (l, Ghost, t, x, ps, co, ss, Instance, vis, false))
     | [< binding = (parser [< '(_, Kwd "static") >] -> Static | [< >] -> Instance); t = parse_type; '(l, Ident x); '(_, Kwd ";") >] ->
       FieldMember [Field (l, Ghost, t, x, binding, vis, false, None)]
     end;
     mems = parse_ghost_java_members cn
  >] -> m::mems
and
  parse_thrown = parser
  [< tp = parse_type; '(_, Kwd "/*@"); '(_, Kwd "ensures"); epost = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> (tp, epost)
and
  parse_throws_clause = parser
  [< '(l, Kwd "throws"); epost = rep_comma parse_thrown >] -> epost
and
  parse_array_dims t = parser
  [< '(l, Kwd "["); '(_, Kwd "]"); t = parse_array_dims (ArrayTypeExpr (l, t)) >] -> t
| [< >] -> t
and 
  id x = parser [< >] -> x
and 
  parse_java_modifier = parser [< '(_, Kwd "public") >] -> VisibilityModifier(Public) | [< '(_, Kwd "protected") >] -> VisibilityModifier(Protected) | [< '(_, Kwd "private") >] -> VisibilityModifier(Private) | [< '(_, Kwd "static") >] -> StaticModifier | [< '(_, Kwd "final") >] -> FinalModifier | [< '(_, Kwd "abstract") >] -> AbstractModifier
and
  parse_java_member cn = parser
  [< modifiers = rep parse_java_modifier;
     binding = (fun _ -> if List.mem StaticModifier modifiers then Static else Instance);
     final = (fun _ -> List.mem FinalModifier modifiers);
     abstract = (fun _ -> List.mem AbstractModifier modifiers);
     vis = (fun _ -> (match (try_find (function VisibilityModifier(_) -> true | _ -> false) modifiers) with None -> Package | Some(VisibilityModifier(vis)) -> vis));
     t = parse_return_type;
     member = parser
       [< '(l, Ident x);
          member = parser
            [< (ps, co, ss) = parse_method_rest >] ->
            let ps = if binding = Instance then (IdentTypeExpr (l, None, cn), "this")::ps else ps in
            MethMember (Meth (l, Real, t, x, ps, co, ss, binding, vis, abstract))
          | [< t = id (match t with None -> raise (ParseException (l, "A field cannot be void.")) | Some(t) -> t);
               tx = parse_array_braces t;
               init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
               ds = comma_rep (parse_declarator t); '(_, Kwd ";")
            >] ->
            let fds =
              ((l, tx, x, init, ref false)::ds) |> List.map begin fun (l, tx, x, init, _) ->
                Field (l, Real, tx, x, binding, vis, final, init)
              end
            in
            FieldMember fds
       >] -> member
     | [< (ps, co, ss) = parse_method_rest >] ->
       let l =
         match t with
           None -> raise (Stream.Error "Keyword 'void' cannot be followed by a parameter list.")
         | Some (IdentTypeExpr (l, None, x)) -> if x = cn then l else raise (ParseException (l, "Constructor name does not match class name."))
         | Some t -> raise (ParseException (type_expr_loc t, "Constructor name expected."))
       in
       if binding = Static then raise (ParseException (l, "A constructor cannot be static."));
       if final then raise (ParseException (l, "A constructor cannot be final."));
       ConsMember (Cons (l, ps, co, ss, vis))
  >] -> member
and parse_array_init_rest = parser
  [< '(_, Kwd ","); es = opt(parser [< e = parse_expr; es = parse_array_init_rest >] -> e :: es) >] -> (match es with None -> [] | Some(es) -> es)
| [< >] -> []
and parse_array_init = parser
  [< '(_, Kwd ","); '(_, Kwd "}") >] -> []
| [< '(_, Kwd "}") >] -> []
| [< e = parse_expr; es = parse_array_init_rest; '(_, Kwd "}") >] -> e :: es
and parse_declaration_rhs te = parser
  [< '(linit, Kwd "{"); es = parse_array_init >] ->
  (match te with ArrayTypeExpr (_, elem_te) -> NewArrayWithInitializer (linit, elem_te, es) | _ -> InitializerList (linit, es))
| [< e = parse_expr >] -> e
and
  parse_declarator t = parser
  [< '(l, Ident x);
     tx = parse_array_braces t;
     init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
  >] -> (l, tx, x, init, ref false)
and
  parse_method_rest = parser
  [< ps = parse_paramlist;
    epost = opt parse_throws_clause;
    (ss, co) = parser
      [< '(_, Kwd ";"); spec = opt parse_spec >] -> (None, spec)
    | [< spec = opt parse_spec; ss = parse_some_block >] -> (ss, spec)
    >] -> (ps, (match co with None -> None | Some(pre, post) -> Some (pre, post, (match epost with None -> [] | Some(epost) -> epost))), ss)
and
  parse_functype_paramlists = parser
  [< ps1 = parse_paramlist; ps2 = opt parse_paramlist >] -> (match ps2 with None -> ([], ps1) | Some ps2 -> (ps1, ps2))
and
  (** Parses
   * /*@<ttparams>(tparams)@*/(params) where
   * <ttparams> and (tparams) and /*@<ttparams>(tparams)@*/ are optional
   *)
  parse_functypedecl_paramlist_in_real_context = parser
  [< '(_, Kwd "/*@");
     functiontypetypeparams = opt parse_type_params_free;
     functiontypeparams = opt parse_paramlist;
     '(_, Kwd "@*/");
     params = parse_paramlist
  >] ->
    let noneToEmptyList value = 
      match value with 
        None -> []
        | Some x -> x
    in
    (noneToEmptyList functiontypetypeparams, noneToEmptyList functiontypeparams, params)
  | [< params = parse_paramlist >] -> ([], [], params)
and
  parse_decl = parser
  [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, Some fs)
  | [< '(_, Kwd ";") >] -> Struct (l, s, None)
  | [< t = parse_type_suffix (StructTypeExpr (l, s)); d = parse_func_rest Regular (Some t) Public >] -> d
  >] -> [d]
| [< '(l, Kwd "typedef");
     rt = parse_return_type; '(_, Ident g);
     ds = begin parser
       [<
         (tparams, ftps, ps) = parse_functypedecl_paramlist_in_real_context;
         '(_, Kwd ";");
         spec = opt parse_spec
       >] ->
         let spec = match spec with
           Some spec -> spec
           | None -> raise (ParseException (l, "Function type declaration should have contract."))
         in
         [FuncTypeDecl (l, Real, rt, g, tparams, ftps, ps, spec)]
       | [< '(_, Kwd ";") >] ->
         begin
           match rt with
             None -> raise (ParseException (l, "Void not allowed here."))
             | Some te -> [TypedefDecl (l, te, g)]
         end
    end
  >] -> ds
| [< '(_, Kwd "enum"); '(l, Ident n); '(_, Kwd "{");
     elems = rep_comma (parser [< '(_, Ident e); init = opt (parser [< '(_, Kwd "="); e = parse_expr >] -> e) >] -> (e, init));
     '(_, Kwd "}"); '(_, Kwd ";"); >] ->
  [EnumDecl(l, n, elems)]
| [< '(_, Kwd "static"); t = parse_return_type; d = parse_func_rest Regular t Private >] -> [d]
| [< t = parse_return_type; d = parse_func_rest Regular t Public >] -> [d]
and
  parse_pure_decls = parser
  [< ds0 = parse_pure_decl; ds = parse_pure_decls >] -> ds0 @ ds
| [< >] -> []
and
  parse_index_list = parser
  [< '(_, Kwd "("); is = rep_comma (parser 
    [< '(l, Ident i); e=parser
      [<'(_, Kwd ".");'(_, Kwd "class")>]-> (l,i)
      |[<>]->(l,i)>] -> e); '(_, Kwd ")") >] -> is
and
  parse_type_params l = parser
    [< xs = parse_angle_brackets l (rep_comma (parser [< '(_, Ident x) >] -> x)) >] -> xs
  | [< >] -> []
and
  parse_pred_body = parser
    [< '(_, Kwd "requires"); p = parse_pred >] -> p
  | [< '(_, Kwd "="); p = parse_pred >] -> p
and
  parse_pred_paramlist = parser
    [< 
      '(_, Kwd "("); ps = rep_comma parse_param;
      (ps, inputParamCount) = (parser [< '(_, Kwd ";"); ps' = rep_comma parse_param >] -> (ps @ ps', Some (List.length ps)) | [< >] -> (ps, None)); '(_, Kwd ")")
    >] -> (ps, inputParamCount)
and
  parse_pure_decl = parser
    [< '(l, Kwd "inductive"); '(li, Ident i); tparams = parse_type_params li; '(_, Kwd "="); cs = (parser [< cs = parse_ctors >] -> cs | [< cs = parse_ctors_suffix >] -> cs); '(_, Kwd ";") >] -> [Inductive (l, i, tparams, cs)]
  | [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t Public>] -> [d]
  | [< '(l, Kwd "predicate"); '(li, Ident g); tparams = parse_type_params li; 
     (ps, inputParamCount) = parse_pred_paramlist;
     body = opt parse_pred_body;
     '(_, Kwd ";");
    >] ->
    [PredFamilyDecl (l, g, tparams, 0, List.map (fun (t, p) -> t) ps, inputParamCount)] @
    (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
  | [< '(l, Kwd "predicate_family"); '(_, Ident g); is = parse_paramlist; (ps, inputParamCount) = parse_pred_paramlist; '(_, Kwd ";") >]
  -> [PredFamilyDecl (l, g, [], List.length is, List.map (fun (t, p) -> t) ps, inputParamCount)]
  | [< '(l, Kwd "predicate_family_instance"); '(_, Ident g); is = parse_index_list; ps = parse_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredFamilyInstanceDecl (l, g, [], is, ps, p)]
  | [< '(l, Kwd "predicate_ctor"); '(_, Ident g); ps1 = parse_paramlist; (ps2, inputParamCount) = parse_pred_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredCtorDecl (l, g, ps1, ps2, inputParamCount, p)]
  | [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest (Lemma(false, None)) t Public >] -> [d]
  | [< '(l, Kwd "lemma_auto"); trigger = opt (parser [< '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); >] -> e); t = parse_return_type; d = parse_func_rest (Lemma(true, trigger)) t Public >] -> [d]
  | [< '(l, Kwd "box_class"); '(_, Ident bcn); ps = parse_paramlist;
       '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";");
       ads = parse_action_decls; hpds = parse_handle_pred_decls; '(_, Kwd "}") >] -> [BoxClassDecl (l, bcn, ps, inv, ads, hpds)]
  | [< '(l, Kwd "typedef"); '(_, Kwd "lemma"); rt = parse_return_type; '(li, Ident g); tps = parse_type_params li;
       (ftps, ps) = parse_functype_paramlists; '(_, Kwd ";"); (pre, post) = parse_spec >] ->
    [FuncTypeDecl (l, Ghost, rt, g, tps, ftps, ps, (pre, post))]
  | [< '(l, Kwd "unloadable_module"); '(_, Kwd ";") >] -> [UnloadableModuleDecl l]
  | [< '(l, Kwd "load_plugin"); '(lx, Ident x); '(_, Kwd ";") >] -> [LoadPluginDecl (l, lx, x)]
  | [< '(l, Kwd "import_module"); '(_, Ident g); '(lx, Kwd ";") >] -> [ImportModuleDecl (l, g)]
  | [< '(l, Kwd "require_module"); '(_, Ident g); '(lx, Kwd ";") >] -> [RequireModuleDecl (l, g)]
and
  parse_action_decls = parser
  [< ad = parse_action_decl; ads = parse_action_decls >] -> ad::ads
| [< >] -> []
and
  parse_action_decl = parser
  [< '(l, Kwd "action"); permbased = opt (parser [< '(_, Kwd "permbased") >] -> 0); '(_, Ident an); ps = parse_paramlist; '(_, Kwd ";");
     '(_, Kwd "requires"); pre = parse_expr; '(_, Kwd ";");
     '(_, Kwd "ensures"); post = parse_expr; '(_, Kwd ";") >] -> ActionDecl (l, an, (match permbased with None -> false | Some _ -> true), ps, pre, post)
and
  parse_handle_pred_decls = parser
  [< hpd = parse_handle_pred_decl; hpds = parse_handle_pred_decls >] -> hpd::hpds
| [< >] -> []
and
  parse_handle_pred_decl = parser
  [< '(l, Kwd "handle_predicate"); '(_, Ident hpn); ps = parse_paramlist;
     extends = opt (parser [< '(l, Kwd "extends"); '(_, Ident ehn) >] -> ehn);
     '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";"); pbcs = parse_preserved_by_clauses; '(_, Kwd "}") >]
     -> HandlePredDecl (l, hpn, ps, extends, inv, pbcs)
and
  parse_preserved_by_clauses = parser
  [< pbc = parse_preserved_by_clause; pbcs = parse_preserved_by_clauses >] -> pbc::pbcs
| [< >] -> []
and
  parse_preserved_by_clause = parser
  [< '(l, Kwd "preserved_by"); '(_, Ident an); '(_, Kwd "("); xs = rep_comma (parser [< '(_, Ident x) >] -> x); '(_, Kwd ")");
     ss = parse_block >] -> PreservedByClause (l, an, xs, ss)
and
  parse_type_params_free = parser [< '(_, Kwd "<"); xs = rep_comma (parser [< '(_, Ident x) >] -> x); '(_, Kwd ">") >] -> xs
and
  parse_type_params_general = parser
  [< xs = parse_type_params_free >] -> xs
| [<
    xs = peek_in_ghost_range (
      parser [<
        xs = parse_type_params_free;
        '(_, Kwd "@*/")
      >] -> xs
    )
  >] -> xs
| [< >] -> []
and
  parse_func_rest k t v = parser
  [<
    '(l, Ident g);
    tparams = parse_type_params_general;
    decl = parser
      [<
        ps = parse_paramlist;
        f = parser
          [< '(_, Kwd ";"); (nonghost_callers_only, ft, co) = parse_spec_clauses >] ->
          Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, None, Static, v)
        | [< (nonghost_callers_only, ft, co) = parse_spec_clauses; '(_, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
          Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, Some (ss, closeBraceLoc), Static, v)
      >] -> f
    | [<
        () = (fun s -> if k = Regular && tparams = [] && t <> None then () else raise Stream.Failure);
        t = parse_array_braces (get t);
        init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs t >] -> e);
        '(_, Kwd ";")
      >] -> Global (l, t, g, init)
  >] -> decl
and
  parse_ctors_suffix = parser
  [< '(_, Kwd "|"); cs = parse_ctors >] -> cs
| [< >] -> []
and
  parse_ctors = parser
  [< '(l, Ident cn);
     ts = begin
       parser
         [< '(_, Kwd "(");
             ts = rep_comma parse_paramtype_and_name;
             '(_, Kwd ")")
         >] -> ts
       | [< >] -> []
     end;
     cs = parse_ctors_suffix
  >] -> Ctor (l, cn, ts)::cs
and
  parse_paramtype_and_name = parser
  [< t = parse_type;
     paramname_opt = opt (parser
       [< '(_, Ident paramname) >] -> paramname
     )
  >] ->
    let paramname = match paramname_opt with None -> "" | Some(x) -> x in
    (paramname, t)
and
  parse_paramtype = parser [< t = parse_type; _ = opt (parser [< '(_, Ident _) >] -> ()) >] -> t
and
  parse_fields = parser
  [< '(_, Kwd "}") >] -> []
| [< f = parse_field; fs = parse_fields >] -> f::fs
and
  parse_field = parser
  [< '(_, Kwd "/*@"); f = parse_field_core Ghost; '(_, Kwd "@*/") >] -> f
| [< f = parse_field_core Real >] -> f
and
  parse_field_core gh = parser
  [< te0 = parse_type; '(l, Ident f);
     te = parser
        [< '(_, Kwd ";") >] -> te0
      | [< '(_, Kwd "["); '(ls, Int size); '(_, Kwd "]"); '(_, Kwd ";") >] ->
          (match te0 with (ManifestTypeExpr (_, _) | PtrTypeExpr (_, _)) ->
            if ( (int_of_big_int size) <= 0 ) then
              raise (ParseException (ls, "Array must have size > 0."));
            StaticArrayTypeExpr (l, te0, (int_of_big_int size))
          | _ -> raise (ParseException (l, "Array cannot be of this type.")))
   >] -> Field (l, gh, te, f, Instance, Public, false, None)
and
  parse_return_type = parser
  [< t = parse_type >] -> match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t
and
  parse_type = parser
  [< t0 = parse_primary_type; t = parse_type_suffix t0 >] -> t
and
  parse_primary_type = parser
  [< '(l, Kwd "volatile"); t0 = parse_primary_type >] -> t0
| [< '(l, Kwd "const"); t0 = parse_primary_type >] -> t0
| [< '(l, Kwd "register"); t0 = parse_primary_type >] -> t0
| [< '(l, Kwd "struct"); '(_, Ident s) >] -> StructTypeExpr (l, s)
| [< '(l, Kwd "enum"); '(_, Ident _) >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "int") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "short") >] -> ManifestTypeExpr(l, ShortType)
| [< '(l, Kwd "long") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "signed"); t0 = parse_primary_type >] ->
  (match t0 with
     (ManifestTypeExpr (_, IntType) | ManifestTypeExpr (_, ShortType) |
      ManifestTypeExpr (_, Char)) -> t0
   | _ -> raise (ParseException (l, "This type cannot be signed.")))
| [< '(l, Kwd "unsigned"); t0 = parse_primary_type >] ->
  (match t0 with
     ManifestTypeExpr (l, IntType) -> ManifestTypeExpr (l, UintPtrType)
   | ManifestTypeExpr (l, ShortType) -> ManifestTypeExpr (l, UShortType)
   | ManifestTypeExpr (l, Char) -> ManifestTypeExpr (l, UChar)
   | _ -> raise (ParseException (l, "This type cannot be unsigned.")))
| [< '(l, Kwd "uintptr_t") >] -> ManifestTypeExpr (l, UintPtrType)
| [< '(l, Kwd "real") >] -> ManifestTypeExpr (l, RealType)
| [< '(l, Kwd "bool") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "boolean") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "void") >] -> ManifestTypeExpr (l, Void)
| [< '(l, Kwd "char") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "byte") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "predicate");
     '(_, Kwd "(");
     ts = rep_comma parse_paramtype;
     ts' = opt (parser [< '(_, Kwd ";"); ts' = rep_comma parse_paramtype >] -> ts');
     '(_, Kwd ")")
  >] -> begin match ts' with None -> PredTypeExpr (l, ts, None) | Some ts' -> PredTypeExpr (l, ts @ ts', Some (List.length ts)) end
| [< '(l, Kwd "fixpoint"); '(_, Kwd "("); ts = rep_comma parse_paramtype; '(_, Kwd ")") >] -> PureFuncTypeExpr (l, ts)
| [< '(l, Kwd "box") >] -> ManifestTypeExpr (l, BoxIdType)
| [< '(l, Kwd "handle") >] -> ManifestTypeExpr (l, HandleIdType)
| [< '(l, Kwd "any") >] -> ManifestTypeExpr (l, AnyType)
| [< '(l, Ident n); rest = rep(parser [< '(l, Kwd "."); '(l, Ident n) >] -> n); targs = parse_type_args l;  >] -> 
    if targs <> [] then 
      match rest with
      | [] ->  ConstructedTypeExpr (l, n, targs) 
      | _ -> raise (ParseException (l, "Package name not supported for generic types."))
    else
      match rest with
        [] -> IdentTypeExpr(l, None, n)
      | _ -> 
      let pac = (String.concat "." (n :: (take ((List.length rest) -1) rest))) in
      IdentTypeExpr(l, Some (pac), List.nth rest ((List.length rest) - 1))
and
  parse_type_suffix t0 = parser
  [< '(l, Kwd "*"); t = parse_type_suffix (PtrTypeExpr (l, t0)) >] -> t
| [< '(l, Kwd "["); '(_, Kwd "]"); t = parse_type_suffix (ArrayTypeExpr (l,t0)) >] -> t
| [< >] -> t0
and
(* parse function parameters: *)
  parse_paramlist =
  parser
    [< '(_, Kwd "("); ps = rep_comma parse_param; '(_, Kwd ")") >] ->
    List.filter filter_void_params ps
and
  filter_void_params ps = match ps with
    (ManifestTypeExpr (_, Void), "") -> false
  | _ -> true
and
  parse_param = parser [< t = parse_type; pn = parse_param_name;
      is_array = opt(parser [< '(l0, Kwd "[");'(_, Kwd "]") >] -> l0);
      (* A basic parser for the parameters of a function signature in a
         function pointer declaration, currenly supporting one parameter: *)
      fp_params = opt(parser [< '(l1, Kwd "("); fpp0 = parse_type;
        '(_, Kwd ")") >] -> fpp0) >] ->
    begin match t with
      ManifestTypeExpr (_, Void) -> 
      begin match pn with
        None -> (t, "")
      | Some((l, pname)) -> raise (ParseException (l, "A parameter cannot be of type void."))
      end
    | _ -> 
      begin match pn with
        None -> raise (ParseException (type_expr_loc t, "Illegal parameter."));
      | Some((l, pname)) -> 
        begin match is_array with
          None -> ( match fp_params with 
                      None -> (t, pname)
                    | Some(_) -> (t, pname) )
        | Some(_) -> (ArrayTypeExpr(type_expr_loc t, t), pname)
        end
      end
    end
  | [< '(l, Kwd "...") >] -> (ConstructedTypeExpr (l, "list", [IdentTypeExpr (l, None, "vararg")]), "varargs")
and
  parse_param_name = parser
    [< '(l, Ident pn) >] -> Some (l, pn)
  | [< '(l, Kwd "("); '(l, Kwd "*"); '(l, Ident pn); '(l, Kwd ")") >] -> 
     Some (l, pn) (* function pointer identifier *)
  | [< >] -> None
and
  parse_functypeclause_args = parser
  [< '(_, Kwd "("); args = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")") >] -> args
| [< >] -> []
and
  parse_pure_spec_clause = parser
  [< '(_, Kwd "nonghost_callers_only") >] -> NonghostCallersOnlyClause
| [< '(_, Kwd ":"); '(li, Ident ft); targs = parse_type_args li; ftargs = parse_functypeclause_args >] -> FuncTypeClause (ft, targs, ftargs)
| [< '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";") >] -> RequiresClause p
| [< '(_, Kwd "ensures"); p = parse_pred; '(_, Kwd ";") >] -> EnsuresClause p
and
  parse_spec_clause = parser
  [< '((sp1, _), Kwd "/*@"); c = parse_pure_spec_clause; '((_, sp2), Kwd "@*/") >] -> c
| [< c = parse_pure_spec_clause >] -> c
and
  parse_spec_clauses = fun token_stream ->
    let in_count = ref 0 in
    let out_count = ref 0 in
    let clause_stream = Stream.from (fun _ -> try let clause = Some (parse_spec_clause token_stream) in in_count := !in_count + 1; clause with Stream.Failure -> None) in
    let nonghost_callers_only = (parser [< 'NonghostCallersOnlyClause >] -> out_count := !out_count + 1; true | [< >] -> false) clause_stream in
    let ft = (parser [< 'FuncTypeClause (ft, fttargs, ftargs) >] -> out_count := !out_count + 1; Some (ft, fttargs, ftargs) | [< >] -> None) clause_stream in
    let pre_post = (parser [< 'RequiresClause pre; 'EnsuresClause post; >] -> out_count := !out_count + 2; Some (pre, post) | [< >] -> None) clause_stream in
    if !in_count > !out_count then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: nonghost_callers_only clause (optional), function type clause (optional), contract (optional).");
    (nonghost_callers_only, ft, pre_post)
and
  parse_spec = parser
    [< (nonghost_callers_only, ft, pre_post) = parse_spec_clauses >] ->
    match (nonghost_callers_only, ft, pre_post) with
      (false, None, None) -> raise Stream.Failure
    | (false, None, (Some (pre, post))) -> (pre, post)
    | _ -> raise (Stream.Error "Incorrect kind, number, or order of specification clauses. Expected: requires clause, ensures clause.")
and
  parse_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> ss
and
  parse_some_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] -> Some (ss,closeBraceLoc)
| [<>] -> None
and
  parse_block_stmt = parser
  [< '(l, Kwd "{");
     (l, ds, ss, locals_to_free) = (parser
       [< '((sp1, _), Kwd "/*@");
          b = parser
          | [< d = parse_pure_decl; ds = parse_pure_decls; '(_, Kwd "@*/"); ss = parse_stmts >] -> (l, d @ ds, ss, ref [])
          | [< s = parse_stmt0; '((_, sp2), Kwd "@*/"); ss = parse_stmts >] -> (l, [], PureStmt ((sp1, sp2), s)::ss, ref [])
       >] -> b
     | [< ds = parse_pure_decls; ss = parse_stmts >] -> (l, ds, ss, ref []));
     '(closeBraceLoc, Kwd "}")
  >] -> BlockStmt(l, ds, ss, closeBraceLoc, locals_to_free)
and
  parse_stmts = parser
  [< s = parse_stmt; ss = parse_stmts >] -> s::ss
| [< >] -> []
and
  parse_stmt = parser [< s = parse_stmt0 >] -> stats#stmtParsed; s
and
  parse_coef = parser
  [< '(l, Kwd "["); pat = parse_pattern; '(_, Kwd "]") >] -> pat
and parse_producing_handle_predicate = parser
  [< '(lph, Ident post_hpn); post_hp_args = parse_arglist; >] -> (lph, post_hpn, post_hp_args)
and
  parse_producing_handle_predicate_list = parser
  [< '(l, Kwd "if"); '(_, Kwd "("); condition = parse_expr; '(_, Kwd ")"); (lph, post_hpn, post_hp_args) = parse_producing_handle_predicate; '(_, Kwd "else"); rest = parse_producing_handle_predicate_list >] -> ConditionalProducingHandlePredicate(lph, condition, post_hpn, post_hp_args, rest); 
| [< (lph, post_hpn, post_hp_args) = parse_producing_handle_predicate >] -> BasicProducingHandlePredicate(lph, post_hpn, post_hp_args)
and
  parse_stmt0 = parser
  [< '((sp1, _), Kwd "/*@"); s = parse_stmt0; '((_, sp2), Kwd "@*/") >] -> PureStmt ((sp1, sp2), s)
| [< '((sp1, _), Kwd "@*/"); s = parse_stmt; '((_, sp2), Kwd "/*@") >] -> NonpureStmt ((sp1, sp2), false, s)
| [< '(l, Kwd "if"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); s1 = parse_stmt;
     s = parser
       [< '(_, Kwd "else"); s2 = parse_stmt >] -> IfStmt (l, e, [s1], [s2])
     | [< >] -> IfStmt (l, e, [s1], [])
  >] -> s
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); sscs = parse_switch_stmt_clauses; '(_, Kwd "}") >] -> SwitchStmt (l, e, sscs)
| [< '(l, Kwd "assert"); p = parse_pred; '(_, Kwd ";") >] -> Assert (l, p)
| [< '(l, Kwd "leak"); p = parse_pred; '(_, Kwd ";") >] -> Leak (l, p)
| [< '(l, Kwd "open"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, targs, es1, es2, Static) ->
       stats#openParsed;
       Open (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       stats#openParsed;
       Open (l, Some target, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [< '(l, Kwd "close"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, targs, es1, es2, Static) ->
       stats#closeParsed;
       Close (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       stats#closeParsed;
       Close (l, Some target, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of close statement must be call expression.")))
| [< '(l, Kwd "split_fraction"); '(li, Ident p); targs = parse_type_args li; pats = parse_patlist;
     coefopt = (parser [< '(_, Kwd "by"); e = parse_expr >] -> Some e | [< >] -> None);
     '(_, Kwd ";") >] -> SplitFractionStmt (l, p, targs, pats, coefopt)
| [< '(l, Kwd "merge_fractions"); a = parse_pred; '(_, Kwd ";") >]
  -> MergeFractionsStmt (l, a)
| [< '(l, Kwd "dispose_box"); '(_, Ident bcn); pats = parse_patlist;
     handleClauses = rep (parser [< '(l, Kwd "and_handle"); '(_, Ident hpn); pats = parse_patlist >] -> (l, hpn, pats));
     '(_, Kwd ";") >] -> DisposeBoxStmt (l, bcn, pats, handleClauses)
| [< '(l, Kwd "create_box"); '(_, Ident x); '(_, Kwd "="); '(_, Ident bcn); args = parse_arglist;
     lower_bounds = opt (parser [< '(l, Kwd "above"); es = rep_comma parse_expr >] -> es);
     upper_bounds = opt (parser [< '(l, Kwd "below"); es = rep_comma parse_expr >] -> es);
     handleClauses = rep (parser 
       [< '(l, Kwd "and_handle"); '(_, Ident x); '(_, Kwd "="); '(_, Ident hpn); args = parse_arglist >] -> (l, x, false, hpn, args)
     | [< '(l, Kwd "and_fresh_handle"); '(_, Ident x); '(_, Kwd "="); '(_, Ident hpn); args = parse_arglist >] -> (l, x, true, hpn, args)
     );
     '(_, Kwd ";")
     >] -> CreateBoxStmt (l, x, bcn, args, (match lower_bounds with None -> [] | Some lbs -> lbs), (match upper_bounds with None -> [] | Some ubs -> ubs), handleClauses)
| [< '(l, Kwd "produce_lemma_function_pointer_chunk"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     ftclause = begin parser
       [< '(_, Kwd ":");
          '(li, Ident ftn);
          targs = parse_type_args li;
          args = parse_arglist;
          '(_, Kwd "("); params = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")");
          '(openBraceLoc, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
       Some (ftn, targs, args, params, openBraceLoc, ss, closeBraceLoc)
     | [< >] -> None
     end;
     body = parser
       [< '(_, Kwd ";") >] -> None
     | [< s = parse_stmt >] -> Some s
  >] -> ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause, body)
| [< '(l, Kwd "produce_function_pointer_chunk"); '(li, Ident ftn);
     targs = parse_type_args li;
     '(_, Kwd "("); fpe = parse_expr; '(_, Kwd ")");
     args = parse_arglist;
     '(_, Kwd "("); params = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")");
     '(openBraceLoc, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
  ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc)
| [< '(l, Kwd "goto"); '(_, Ident lbl); '(_, Kwd ";") >] -> GotoStmt (l, lbl)
| [< '(l, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";") >] -> InvariantStmt (l, inv)
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     (inv, dec, body) = parse_loop_core
  >] -> WhileStmt (l, e, inv, dec, body)
| [< '(l, Kwd "do"); (inv, dec, body) = parse_loop_core; '(lwhile, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] ->
  (* "do S while (E);" is translated to "while (true) { S if (E) {} else break; }" *)
  (* CAVEAT: If we ever add support for 'continue' statements, then this translation is not sound. *)
  WhileStmt (l, True l, inv, dec, body @ [IfStmt (lwhile, e, [], [Break lwhile])])
| [< '(l, Kwd "for");
     '(_, Kwd "(");
     init_stmts = begin parser
       [< e = parse_expr;
          ss = parser
            [< '(l, Ident x); s = parse_decl_stmt_rest (type_expr_of_expr e) l x >] -> [s]
          | [< es = comma_rep parse_expr; '(_, Kwd ";") >] -> List.map (fun e -> ExprStmt e) (e::es)
       >] -> ss
     | [< te = parse_type; '(l, Ident x); s = parse_decl_stmt_rest te l x >] -> [s]
     | [< '(_, Kwd ";") >] -> []
     end;
     cond = opt parse_expr;
     '(_, Kwd ";");
     update_exprs = rep_comma parse_expr;
     '(_, Kwd ")");
     (inv, dec, b) = parse_loop_core
  >] ->
  let cond = match cond with None -> True l | Some e -> e in
  BlockStmt (l, [], init_stmts @ [WhileStmt (l, cond, inv, dec, b @ List.map (fun e -> ExprStmt e) update_exprs)], l, ref [])
| [< '(l, Kwd "throw"); e = parse_expr; '(_, Kwd ";") >] -> Throw (l, e)
| [< '(l, Kwd "break"); '(_, Kwd ";") >] -> Break(l)
| [< '(l, Kwd "try");
     body = parse_block;
     catches = rep (parser [< '(l, Kwd "catch"); '(_, Kwd "("); t = parse_type; '(_, Ident x); '(_, Kwd ")"); body = parse_block >] -> (l, t, x, body));
     finally = opt (parser [< '(l, Kwd "finally"); body = parse_block >] -> (l, body))
  >] ->
  begin match (catches, finally) with
    ([], Some (lf, finally)) -> TryFinally (l, body, lf, finally)
  | (catches, None) -> TryCatch (l, body, catches)
  | (catches, Some (lf, finally)) -> TryFinally (l, [TryCatch (l, body, catches)], lf, finally)
  end
| [< s = parse_block_stmt >] -> s
| [< '(lcb, Kwd "consuming_box_predicate"); '(_, Ident pre_bpn); pre_bp_args = parse_patlist;
     consumed_handle_predicates = rep(parser
       [< '(lch, Kwd "consuming_handle_predicate"); '(_, Ident pre_hpn); pre_hp_args = parse_patlist; >] -> ConsumingHandlePredicate(lch, pre_hpn, pre_hp_args)
     );
     '(lpa, Kwd "perform_action"); '(_, Ident an); aargs = parse_arglist;
     '(_, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}");
     post_bp_args =
       opt
         begin
           parser
             [< '(lpb, Kwd "producing_box_predicate"); '(_, Ident post_bpn); post_bp_args = parse_arglist >] ->
             if post_bpn <> pre_bpn then raise (ParseException (lpb, "The box predicate name cannot change."));
             (lpb, post_bp_args)
         end;
     produced_handles = rep(parser
       [< '(_, Kwd "producing_handle_predicate"); producing_hp_list = parse_producing_handle_predicate_list >] -> (false, producing_hp_list)
     | [< '(_, Kwd "producing_fresh_handle_predicate"); producing_hp_list = parse_producing_handle_predicate_list >] -> (true, producing_hp_list));
     '(_, Kwd ";") >] ->
     PerformActionStmt (lcb, ref false, pre_bpn, pre_bp_args, consumed_handle_predicates, lpa, an, aargs, ss, closeBraceLoc, post_bp_args, produced_handles)
| [< '(l, Kwd ";") >] -> NoopStmt l
| [< '(l, Kwd "super"); s = parser 
     [< '(_, Kwd "."); '(l2, Ident n); '(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")") >] -> ExprStmt(SuperMethodCall (l, n, es))
   | [<'(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] -> SuperConstructorCall (l, es)
  >] -> s
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] ->
    begin match e with
      AssignExpr (l, Operation (llhs, Mul, [Var (lt, t, _); Var (lx, x, _)], _), rhs) -> DeclStmt (l, [l, PtrTypeExpr (llhs, IdentTypeExpr (lt, None, t)), x, Some(rhs), ref false])
    | _ -> ExprStmt e
    end
  | [< '(l, Kwd ":") >] -> (match e with Var (_, lbl, _) -> LabelStmt (l, lbl) | _ -> raise (ParseException (l, "Label must be identifier.")))
  | [< '(lx, Ident x); s = parse_decl_stmt_rest (type_expr_of_expr e) lx x >] -> s
  >] -> s
(* parse variable declarations: *)
| [< te = parse_type; '(lx, Ident x); s2 = parse_decl_stmt_rest te lx x >] ->
  ( try match te with
     ManifestTypeExpr (l, Void) ->
      raise (ParseException (l, "A variable cannot be of type void."))
    with
     Match_failure _ -> s2 )
and
  parse_loop_core = parser [<
    (inv, dec) = parse_loop_core0;
    body = parse_stmt
  >] -> (inv, dec, [body])
and
  parse_loop_core0 = parser [<
    inv =
      opt
        begin parser
          [< '(_, Kwd "/*@");
             inv = begin parser
               [< '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> LoopInv p
             | [< '(_, Kwd "requires"); pre = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/");
                  '(_, Kwd "/*@"); '(_, Kwd "ensures"); post = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> LoopSpec (pre, post)
             end
          >] -> inv
        | [< '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); >] -> LoopInv p
        end;
    dec = opt (parser [< '(_, Kwd "/*@"); '(_, Kwd "decreases"); decr = parse_expr; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> decr | [< '(_, Kwd "decreases"); decr = parse_expr; '(_, Kwd ";"); >] -> decr );(* only allows decreases if invariant provided *)
  >] -> (inv, dec)
and
  packagename_of_read l e =
  match e with
  | Var(_, x, _) when x <> "this" -> x
  | Read(_, e, f) -> (packagename_of_read l e) ^ "." ^ f
  | e -> raise (ParseException (l, "Type expected."))
and
  type_expr_of_expr e =
  match e with
    Var (l, x, _) -> IdentTypeExpr (l, None, x)
  | CallExpr (l, x, targs, [], [], Static) -> ConstructedTypeExpr (l, x, targs)
  | ArrayTypeExpr' (l, e) -> ArrayTypeExpr (l, type_expr_of_expr e)
  | Read(l, e, name) -> IdentTypeExpr(l, Some(packagename_of_read l e), name)
  | e -> raise (ParseException (expr_loc e, "Type expected."))
and parse_array_braces te = parser
  [< '(l, Kwd "[");
     te = begin parser
       [< '(lsize, Int size) >] ->
       if sign_big_int size <= 0 then raise (ParseException (lsize, "Array must have size > 0."));
       StaticArrayTypeExpr (l, te, int_of_big_int size)
     | [< >] ->
       ArrayTypeExpr (l, te)
     end;
     '(_, Kwd "]") >] -> te
| [< >] -> te
and parse_create_handle_keyword = parser 
    [< '(l, Kwd "create_handle") >] -> (l, false)
  | [< '(l, Kwd "create_fresh_handle") >] -> (l, true)
and
  parse_decl_stmt_rest te lx x = parser
    [< '(l, Kwd "=");
       s = parser
         [< (l, fresh) = parse_create_handle_keyword; '(_, Ident hpn); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] ->
         begin
           match te with ManifestTypeExpr (_, HandleIdType) -> () | _ -> raise (ParseException (l, "Target variable of handle creation statement must have type 'handle'."))
         end;
         CreateHandleStmt (l, x, fresh, hpn, e)
       | [< rhs = parse_declaration_rhs te; ds = comma_rep (parse_declarator te); '(_, Kwd ";") >] ->
         DeclStmt (l, (l, te, x, Some(rhs), ref false)::ds)
    >] -> s
  | [< tx = parse_array_braces te;
       init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
       ds = comma_rep (parse_declarator te);
       '(_, Kwd ";")
    >] ->
    DeclStmt(type_expr_loc te, (lx, tx, x, init, ref false)::ds)
and
  parse_switch_stmt_clauses = parser
  [< c = parse_switch_stmt_clause; cs = parse_switch_stmt_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_stmt_clause = parser
  [< '(l, Kwd "case"); e = parse_expr; '(_, Kwd ":"); ss = parse_stmts >] -> SwitchStmtClause (l, e, ss)
| [< '(l, Kwd "default"); '(_, Kwd ":"); ss = parse_stmts; >] -> SwitchStmtDefaultClause(l, ss)
and
  parse_more_pats = parser
  [< '(_, Kwd ")") >] -> []
| [< '(_, Kwd ","); '(lx, Ident x); xs = parse_more_pats >] -> x::xs
and
  parse_pred = parser
  [< p0 = parse_pred0; p = parse_sep_rest p0 >] -> p
and
  parse_sep_rest p1 = parser
  [< '(l, Kwd "&*&"); p2 = parse_pred >] -> Sep (l, p1, p2)
| [< >] -> p1
and
  pat_of_expr e =
  match e with
    CallExpr (l, g, [], [], pats, Static) when List.exists (function LitPat _ -> false | _ -> true) pats ->
    CtorPat (l, g, pats)
  | _ -> LitPat e
and
  parse_pred0 = parser
  [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_pred_clauses; '(_, Kwd "}") >] -> SwitchAsn (l, e, cs)
| [< '(l, Kwd "emp") >] -> EmpAsn l
| [< '(l, Kwd "forall_"); '(_, Kwd "("); tp = parse_type; '(_, Ident x); '(_, Kwd ";"); e = parse_expr; '(_, Kwd ")") >] -> ForallAsn(l, tp, x, e)
| [< '(_, Kwd "("); p = parse_pred; '(_, Kwd ")") >] -> p
| [< '(l, Kwd "["); coef = parse_pattern; '(_, Kwd "]"); p = parse_pred0 >] -> CoefAsn (l, coef, p)
| [< '(_, Kwd "#"); '(l, String s) >] -> PluginAsn (l, s)
| [< '(l, Kwd "ensures"); p = parse_pred >] -> EnsuresAsn (l, p)
| [< e = parse_disj_expr; p = parser
    [< '(l, Kwd "|->"); rhs = parse_pattern >] -> 
    (match e with
       ReadArray (_, _, SliceExpr (_, _, _)) -> PointsTo (l, e, rhs)
     | ReadArray (lr, e0, e1) when !language = CLang -> PointsTo (l, Deref(lr, Operation(lr, Add, [e0; e1], ref None), ref None), rhs) 
     | _ -> PointsTo (l, e, rhs)
    )
  | [< '(l, Kwd "?"); p1 = parse_pred; '(_, Kwd ":"); p2 = parse_pred >] -> IfAsn (l, e, p1, p2)
  | [< >] ->
    (match e with
     | CallExpr (l, g, targs, pats0, pats, Static) -> PredAsn (l, new predref g, targs, pats0, pats)
     | CallExpr (l, g, [], pats0, LitPat e::pats, Instance) ->
       let index =
         match pats0 with
           [] -> CallExpr (l, "getClass", [], [], [LitPat e], Instance)
         | [LitPat e] -> e
         | _ -> raise (ParseException (l, "Instance predicate call: single index expression expected"))
       in
       InstPredAsn (l, e, g, index, pats)
     | Operation (l, Eq, [e1; e2], _) ->
       begin match pat_of_expr e2 with
         LitPat e2 -> ExprAsn (l, e)
       | e2 -> MatchAsn (l, e1, e2)
       end
     | _ -> ExprAsn (expr_loc e, e)
    )
  >] -> p
and
  parse_pattern = parser
  [< '(_, Kwd "_") >] -> DummyPat
| [< '(_, Kwd "?"); '(lx, Ident x) >] -> VarPat (lx, x)
| [< '(_, Kwd "^"); e = parse_expr >] -> LitPat (WidenedParameterArgument e)
| [< e = parse_expr >] -> pat_of_expr e
and
  parse_switch_pred_clauses = parser
  [< c = parse_switch_pred_clause; cs = parse_switch_pred_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_pred_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); p = parse_pred; '(_, Kwd ";") >] -> SwitchAsnClause (l, c, pats, ref None, p)
and
  parse_expr stream = parse_assign_expr stream
and
  parse_assign_expr = parser
  [< e0 = parse_cond_expr; e = parse_assign_expr_rest e0 >] -> e
and
  parse_cond_expr = parser
  [< e0 = parse_disj_expr; e = parser
    [< '(l, Kwd "?"); e1 = parse_expr; '(_, Kwd ":"); e2 = parse_cond_expr >] -> IfExpr (l, e0, e1, e2)
  | [< >] -> e0
  >] -> e
and
  parse_disj_expr = parser
  [< e0 = parse_conj_expr; e = parse_disj_expr_rest e0 >] -> e
and
  parse_conj_expr = parser
  [< e0 = parse_bitor_expr; e = parse_conj_expr_rest e0 >] -> e
and
  parse_bitor_expr = parser
  [< e0 = parse_bitxor_expr; e = parse_bitor_expr_rest e0 >] -> e
and
  parse_bitxor_expr = parser
  [< e0 = parse_bitand_expr; e = parse_bitxor_expr_rest e0 >] -> e
and
  parse_bitand_expr = parser
  [< e0 = parse_expr_rel; e = parse_bitand_expr_rest e0 >] -> e
and
  parse_expr_rel = parser
  [< e0 = parse_shift; e = parse_expr_rel_rest e0 >] -> e
and
  parse_shift = parser
  [< e0 = parse_expr_arith; e = parse_shift_rest e0 >] -> e
and
  parse_expr_arith = parser
  [< e0 = parse_expr_mul; e = parse_expr_arith_rest e0 >] -> e
and
  parse_expr_mul = parser
  [< e0 = parse_expr_suffix; e = parse_expr_mul_rest e0 >] -> e
and
  parse_expr_suffix = parser
  [< e0 = parse_expr_primary; e = parse_expr_suffix_rest e0 >] -> e
and
  parse_type_args l = parser
    [< targs = parse_angle_brackets l (rep_comma parse_type) >] -> targs
  | [< >] -> []
and
  parse_new_array_expr_rest l elem_typ = parser
  [< '(_, Kwd "[");
     e = parser
       [< length = parse_expr; '(_, Kwd "]"); >] -> NewArray(l, elem_typ, length)
     | [< '(_, Kwd "]"); '(_, Kwd "{"); es = rep_comma parse_expr; '(_, Kwd "}") >] -> NewArrayWithInitializer (l, elem_typ, es)
  >] -> e
and
  parse_expr_primary = parser
  [< '(l, Kwd "true") >] -> True l
| [< '(l, Kwd "false") >] -> False l
| [< '(l, CharToken c) >] -> IntLit(l, big_int_of_int (Char.code c), ref (Some Char))
| [< '(l, Kwd "null") >] -> Null l
| [< '(l, Kwd "currentThread") >] -> Var (l, "currentThread", ref None)
| [< '(l, Kwd "varargs") >] -> Var (l, "varargs", ref None)
| [< '(l, Kwd "new"); tp = parse_primary_type; res = (parser 
                    [< args0 = parse_patlist >] -> 
                    begin match tp with
                      IdentTypeExpr(_, pac, cn) -> NewObject (l, (match pac with None -> "" | Some(pac) -> pac ^ ".") ^ cn, List.map (function LitPat e -> e | _ -> raise (Stream.Error "Patterns are not allowed in this position")) args0)
                    | _ -> raise (ParseException (type_expr_loc tp, "Class name expected"))
                    end
                  | [< e = parse_new_array_expr_rest l tp >] -> e)
  >] -> res
| [<
    '(lx, Ident x);
    ex = parser
      [<
        args0 = parse_patlist;
        e = parser
          [< args = parse_patlist >] -> CallExpr (lx, x, [], args0, args,Static)
        | [< >] -> CallExpr (lx, x, [], [], args0,Static)
      >] -> e
    | [<
        '(ldot, Kwd ".") when !language = Java;
        r = parser
          [<'(lc, Kwd "class")>] -> ClassLit(ldot,x)
        | [<
            '(lf, Ident f);
            e = parser
              [<args0 = parse_patlist; (args0, args) = (parser [< args = parse_patlist >] -> (args0, args) | [< >] -> ([], args0)) >] ->
              CallExpr (lf, f, [], args0, LitPat(Var(lx,x,ref None))::args,Instance)
            | [<>] -> Read (ldot, Var(lx,x, ref None), f)
          >]->e 
      >]-> r
    | [< >] -> Var (lx, x, ref None)
  >] -> ex
| [< '(l, Int i) >] -> IntLit (l, i, ref None)
| [< '(l, RealToken i) >] -> RealLit (l, num_of_big_int i)
| [< '(l, Kwd "INT_MIN") >] -> IntLit (l, big_int_of_string "-2147483648", ref None)
| [< '(l, Kwd "INT_MAX") >] -> IntLit (l, big_int_of_string "2147483647", ref None)
| [< '(l, Kwd "UINTPTR_MAX") >] -> IntLit (l, big_int_of_string "4294967295", ref None)
| [< '(l, Kwd "UCHAR_MAX") >] -> IntLit (l, big_int_of_string "255", ref None)
| [< '(l, Kwd "USHRT_MAX") >] -> IntLit (l, big_int_of_string "65535", ref None)
| [< '(l, Kwd "UINT_MAX") >] -> IntLit (l, big_int_of_string "4294967295", ref None)
| [< '(l, String s); ss = rep (parser [< '(_, String s) >] -> s) >] -> StringLit (l, String.concat "" (s::ss))
| [< '(l, Kwd "truncating"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, true, t, e)
| [< e = peek_in_ghost_range (parser [< '(l, Kwd "truncating"); '(_, Kwd "@*/"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, true, t, e)) >] -> e
| [< '(l, Kwd "(");
     e = parser
     [< e0 = parse_expr; '(_, Kwd ")");
         e = parser
           [< '(l', Ident y); e = parse_expr_suffix_rest (Var (l', y, ref (Some LocalVar))) >] -> (match e0 with 
             Var (lt, x, _) -> CastExpr (l, false, IdentTypeExpr (lt, None, x), e)
           | _ -> raise (ParseException (l, "Type expression of cast expression must be identifier: ")))
         | [<>] -> e0
     >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, false, te, e)
   >] -> e
(*
| [< '(l, Kwd "(");
     e = parser
     [< e = parse_expr; '(_, Kwd ")") >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e*)
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses;
     cdef_opt = opt (parser [< '(l, Kwd "default"); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> (l, e));
     '(_, Kwd "}")
  >] -> SwitchExpr (l, e, cs, cdef_opt, ref None)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "super"); '(_, Kwd "."); '(l2, Ident n); '(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")") >] -> SuperMethodCall (l, n, es)
| [< '(l, Kwd "!"); e = parse_expr_suffix >] -> Operation(l, Not, [e], ref None)
| [< '(l, Kwd "@"); '(_, Ident g) >] -> PredNameExpr (l, g)
| [< '(l, Kwd "*"); e = parse_expr_suffix >] -> Deref (l, e, ref None)
| [< '(l, Kwd "&"); e = parse_expr_suffix >] -> AddressOf (l, e)
| [< '(l, Kwd "~"); e = parse_expr_suffix >] -> Operation (l, BitNot, [e], ref None)
| [< '(l, Kwd "-"); e = parse_expr_suffix >] ->
  begin match e with
    IntLit (_, n, t) -> IntLit (l, minus_big_int n, t)
  | _ -> Operation (l, Sub, [IntLit (l, zero_big_int, ref None); e], ref None)
  end
| [< '(l, Kwd "++"); e = parse_expr_suffix >] -> AssignOpExpr (l, e, Add, IntLit (l, unit_big_int, ref None), false, ref None, ref None)
| [< '(l, Kwd "--"); e = parse_expr_suffix >] -> AssignOpExpr (l, e, Sub, IntLit (l, unit_big_int, ref None), false, ref None, ref None)
| [< '(l, Kwd "{"); es = rep_comma parse_expr; '(_, Kwd "}") >] -> InitializerList (l, es)
and
  parse_switch_expr_clauses = parser
  [< c = parse_switch_expr_clause; cs = parse_switch_expr_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_expr_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> SwitchExprClause (l, c, pats, e)
and
  expr_to_class_name e =
    match e with
      Var (_, x, _) -> x
    | Read (_, e, f) -> expr_to_class_name e ^ "." ^ f
    | _ -> raise (ParseException (expr_loc e, "Class name expected"))
and
  parse_expr_suffix_rest e0 = parser
  [< '(l, Kwd "->"); '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, f)) >] -> e
| [< '(l, Kwd ".") when !language = CLang; '(_, Ident f); e = parse_expr_suffix_rest (Read (l, AddressOf(l, e0), f)) >] -> e
| [< '(l, Kwd ".");
     e = begin parser
       [< '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, f)) >] -> e
     | [< '(_, Kwd "class"); e = parse_expr_suffix_rest (ClassLit (l, expr_to_class_name e0)) >] -> e
     end
  >] -> e
| [< '(l, Kwd "["); 
     e = begin parser
       [< '(_, Kwd "]") >] -> ArrayTypeExpr' (l, e0)
     | [< p1 = opt parse_pattern;
          e = begin parser
            [< '(ls, Kwd ".."); p2 = opt parse_pattern; '(_, Kwd "]") >] -> ReadArray (l, e0, SliceExpr (ls, p1, p2))
          | [< '(_, Kwd "]") >] -> begin match p1 with Some (LitPat e1) -> ReadArray (l, e0, e1) | _ -> raise (ParseException (l, "Malformed array access.")) end
          end
       >] -> e
     end; e = parse_expr_suffix_rest e >] -> e
| [< '(l, Kwd "++"); e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Add, IntLit (l, unit_big_int, ref None), true, ref None, ref None)) >] -> e
| [< '(l, Kwd "--"); e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Sub, IntLit (l, unit_big_int, ref None), true, ref None, ref None)) >] -> e
| [< '(l, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")"); e = parse_expr_suffix_rest (match e0 with Read(l', e0', f') -> CallExpr (l', f', [], [], LitPat(e0'):: (List.map (fun e -> LitPat(e)) es), Instance) | _ -> ExprCallExpr (l, e0, es)) >] -> e
| [< >] -> e0
and
  parse_expr_mul_rest e0 = parser
  [< '(l, Kwd "*"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Mul, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "/"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Div, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "%"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Mod, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_arith_rest e0 = parser
  [< '(l, Kwd "+"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Add, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "-"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_shift_rest e0 = parser
  [< '(l, Kwd "<<"); e1 = parse_expr_arith; e = parse_shift_rest (Operation (l, ShiftLeft, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd ">>"); e1 = parse_expr_arith; e = parse_shift_rest (Operation (l, ShiftRight, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and

  parse_expr_rel_rest e0 = parser
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd ">"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Lt, [e1; e0], ref None)) >] -> e
| [< '(l, Kwd ">="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e1; e0], ref None)) >] -> e
| [< '(l, Kwd "instanceof"); tp = parse_expr; e = parse_expr_rel_rest (InstanceOfExpr (l, e0, type_expr_of_expr tp)) >] -> e
| [< e = parse_expr_lt_rest e0 parse_expr_rel_rest >] -> e
and
  apply_type_args e targs args =
  match e with
    Var (lx, x, _) -> CallExpr (lx, x, targs, [], args, Static)
  | CastExpr (lc, trunc, te, e) -> CastExpr (lc, trunc, te, apply_type_args e targs args)
  | Operation (l, Not, [e], ts) -> Operation (l, Not, [apply_type_args e targs args], ts)
  | Operation (l, BitNot, [e], ts) -> Operation (l, BitNot, [apply_type_args e targs args], ts)
  | Deref (l, e, ts) -> Deref (l, apply_type_args e targs args, ts)
  | AddressOf (l, e) -> AddressOf (l, apply_type_args e targs args)
  | Operation (l, op, [e1; e2], ts) -> Operation (l, op, [e1; apply_type_args e2 targs args], ts)
  | _ -> raise (ParseException (expr_loc e, "Identifier expected before type argument list"))
and
  parse_expr_lt_rest e0 cont = parser
  [< '(l, Kwd "<");
     e = parser
       [< e1 = parse_expr_arith; e1 = parse_expr_lt_rest e1 (let rec iter e0 = parse_expr_lt_rest e0 iter in iter);
          e = parser
            [< '(_, Kwd ">"); (* Type argument *)
               args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
               e = cont (apply_type_args e0 [type_expr_of_expr e1] args)
            >] -> e
          | [< '(_, Kwd ","); ts = rep_comma parse_type; '(_, Kwd ">");
               args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
               e = cont (apply_type_args e0 ([type_expr_of_expr e1] @ ts) args)
            >] -> e
          | [< e = cont (Operation (l, Lt, [e0; e1], ref None)) >] -> e
       >] -> e
     | [< ts = rep_comma parse_type; '(_, Kwd ">");
          args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
          e = cont (apply_type_args e0 ts args)
       >] -> e
  >] -> e
| [< >] -> e0
and
  parse_bitand_expr_rest e0 = parser
  [< '(l, Kwd "&"); e1 = parse_expr_rel; e = parse_bitand_expr_rest (Operation (l, BitAnd, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_bitxor_expr_rest e0 = parser
  [< '(l, Kwd "^"); e1 = parse_bitand_expr; e = parse_bitxor_expr_rest (Operation (l, BitXor, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_bitor_expr_rest e0 = parser
  [< '(l, Kwd "|"); e1 = parse_bitxor_expr; e = parse_bitor_expr_rest (Operation (l, BitOr, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_conj_expr_rest e0 = parser
  [< '(l, Kwd "&&"); e1 = parse_expr_rel; e = parse_conj_expr_rest (Operation (l, And, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_disj_expr_rest e0 = parser
  [< '(l, Kwd "||"); e1 = parse_conj_expr; e = parse_disj_expr_rest (Operation (l, Or, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_assign_expr_rest e0 = parser
  [< '(l, Kwd "="); e1 = parse_assign_expr >] -> AssignExpr (l, e0, e1)
| [< '(l, Kwd "+="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Add, e1, false, ref None, ref None)
| [< '(l, Kwd "-="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Sub, e1, false, ref None, ref None)
| [< '(l, Kwd "*="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Mul, e1, false, ref None, ref None)
| [< '(l, Kwd "/="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Div, e1, false, ref None, ref None)
| [< '(l, Kwd "&="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, And, e1, false, ref None, ref None)
| [< '(l, Kwd "|="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Or, e1, false, ref None, ref None)
| [< '(l, Kwd "^="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Xor, e1, false, ref None, ref None)
| [< '(l, Kwd "%="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Mod, e1, false, ref None, ref None)
| [< '(l, Kwd "<<="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ShiftLeft, e1, false, ref None, ref None)
| [< '(l, Kwd ">>="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ShiftRight, e1, false, ref None, ref None)
(*| [< '(l, Kwd ">>>="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ???, e1, false, ref None, ref None)*)
| [< >] -> e0
and
  parse_arglist = parser
  [< '(l, Kwd "("); es = parser [< '(_, Kwd ")") >] -> [] | [< e0 = parse_expr; es = parse_arglist_rest >] -> e0::es >] -> es
and
  parse_arglist_rest = parser
  [< '(_, Kwd ","); e0 = parse_expr; es = parse_arglist_rest >] -> e0::es
| [< '(_, Kwd ")") >] -> []
and
  parse_patlist = parser
  [< '(l, Kwd "("); pats = parser [< '(_, Kwd ")") >] -> [] | [< pat0 = parse_pattern; pats = parse_patlist_rest >] -> pat0::pats >] -> pats
and
  parse_patlist_rest = parser
  [< '(_, Kwd ","); pat0 = parse_pattern; pats = parse_patlist_rest >] -> pat0::pats
| [< '(_, Kwd ")") >] -> []

let rec parse_package_name= parser
  [<'(_, Ident n);x=parser
    [<'(_, Kwd ".");rest=parse_package_name>] -> n^"."^rest
  | [<'(_, Kwd ";")>] -> n
  >] -> x
  
let parse_package= parser
  [<'(l, Kwd "package");n= parse_package_name>] ->(l,n)
| [<>] -> (dummy_loc,"")
  
let rec parse_import_names= parser
  [<'(_, Kwd ".");y=parser
        [<'(_, Kwd "*");'(_, Kwd ";")>] -> ("",None)
      | [<'(_, Ident el);x=parser
          [<'(_, Kwd ";")>]-> ("",Some el)
        | [<rest=parse_import_names>]-> let (n',el')=rest in ("."^el^n',el')
        >] -> x
  >] -> y

let parse_import_name= parser
  [<'(_, Ident n);(n',el)=parse_import_names>] -> (n^n',el)
  
let parse_import0= parser
  [<'(l, Kwd "import");n= parse_import_name>] -> let (pn,el)=n in Import(l,pn,el)

let parse_import = parser
  [< i = parse_import0 >] -> i
| [< i = peek_in_ghost_range (parser [< i = parse_import0; '(_, Kwd "@*/") >] -> i) >] -> i

let parse_package_decl= parser
  [< (l,p) = parse_package; is=rep parse_import; ds=parse_decls Java;>] -> PackageDecl(l,p,Import(dummy_loc,"java.lang",None)::is, ds)

let parse_scala_file (path: string) (reportRange: range_kind -> loc -> unit): package =
  let lexer = make_lexer Scala.keywords ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< ds = rep Scala.parse_decl; _ = Stream.empty >] -> PackageDecl(dummy_loc,"",[Import(dummy_loc,"java.lang",None)],ds) in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

(* 
  renamed from parse_java_spec_file to still support spec files, 
  normal java files are now handled by frontend
*)
let parse_java_spec_file (path: string) (reportRange: range_kind -> loc -> unit) reportShouldFail: package =
  Stopwatch.start parsing_stopwatch;
  let result =
  if Filename.check_suffix (Filename.basename path) ".scala" then
    parse_scala_file path reportRange
  else
  let lexer = make_lexer (common_keywords @ java_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange reportShouldFail in
  let parse_decls_eof = parser [< p = parse_package_decl; _ = Stream.empty >] -> p in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

type 'result parser_ = (loc * token) Stream.t -> 'result

let rec parse_include_directives (ignore_eol: bool ref) : ((loc * (include_kind * string * string) * string list * package list) list * string list) parser_ =
  let active_headers = ref [] in
  let test_include_cycle l totalPath =
    if List.mem totalPath !active_headers then raise (ParseException (l, "Include cycles (even with header guards) are not supported"));
  in
  let rec parse_include_directives_core header_names = parser
  | [< (headers, header_name) = parse_include_directive; (headers', header_names') = parse_include_directives_core (header_name::header_names) >] 
          -> (List.append headers headers', header_names')
  | [< >] -> ([], header_names)
  and parse_include_directive = 
    let isGhostHeader header = Filename.check_suffix header ".gh" in
    parser
      [< '(l, SecondaryInclude(h, totalPath)) >] -> test_include_cycle l totalPath; ([], totalPath)
    | [< (l,h,totalPath) = peek_in_ghost_range begin parser [< '(l, SecondaryInclude(h, p)) >] -> (l,h,p) end; '(_, Kwd "@*/") >] -> test_include_cycle l totalPath; ([], totalPath)
    | [< '(l, BeginInclude(kind, h, totalPath)); (headers, header_names) = (active_headers := totalPath::!active_headers; parse_include_directives_core []); 
                                           ds = parse_decls CLang ~inGhostHeader:(isGhostHeader h); '(_, EndInclude) >] -> 
                                                        active_headers := List.filter (fun h -> h <> totalPath) !active_headers;
                                                        let ps = [PackageDecl(dummy_loc,"",[],ds)] in
                                                        (List.append headers [(l, (kind, h, totalPath), header_names, ps)], totalPath)
    | [< (l,kind,h,totalPath) = peek_in_ghost_range begin parser [< '(l, BeginInclude(kind, h, p)) >] -> (l,kind,h,p) end; 
                                                (headers, header_names) = (active_headers := totalPath::!active_headers; parse_include_directives_core []); 
                                                ds = parse_decls CLang ~inGhostHeader:(isGhostHeader h); '(_, EndInclude); '(_, Kwd "@*/") >] -> 
                                                        active_headers := List.filter (fun h -> h <> totalPath) !active_headers;
                                                        let ps = [PackageDecl(dummy_loc,"",[],ds)] in
                                                        (List.append headers [(l, (kind, h, totalPath), header_names, ps)], totalPath)
  in
  parse_include_directives_core []

  let parse_c_file (path: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit) (include_paths: string list): 
                                              ((loc * (include_kind * string * string) * string list * package list) list * package list) = (* ?parse_c_file *)
  Stopwatch.start parsing_stopwatch;
  let result =
    let make_lexer basePath relPath include_paths ~inGhostRange =
      let text = readFile (concat basePath relPath) in
      make_lexer (common_keywords @ c_keywords) ghost_keywords (basePath, relPath) text reportRange ~inGhostRange reportShouldFail
    in
    let (loc, ignore_eol, token_stream) = make_preprocessor make_lexer (Filename.dirname path) (Filename.basename path) include_paths in
    let parse_c_file =
      parser
        [< (headers, _) = parse_include_directives ignore_eol; 
                            ds = parse_decls CLang ~inGhostHeader:false; _ = Stream.empty >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
    in
    try
      parse_c_file token_stream
    with
      Stream.Error msg -> raise (ParseException (loc(), msg))
    | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;  
  result

let parse_header_file (basePath: string) (relPath: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit) 
         (include_paths: string list): ((loc * (include_kind * string * string) * string list * package list) list * package list) =
  Stopwatch.start parsing_stopwatch;
  let isGhostHeader = Filename.check_suffix relPath ".gh" in
  let result =
    let make_lexer basePath relPath include_paths ~inGhostRange =
      let text = readFile (concat basePath relPath) in
      make_lexer (common_keywords @ c_keywords) ghost_keywords (basePath, relPath) text reportRange ~inGhostRange:inGhostRange reportShouldFail
    in
    let (loc, ignore_eol, token_stream) = make_preprocessor make_lexer basePath relPath include_paths in
    let p = parser
      [< (headers, _) = parse_include_directives ignore_eol; ds = parse_decls CLang ~inGhostHeader:isGhostHeader; 
                                                  _ = (fun _ -> ignore_eol := true);_ = Stream.empty >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
    in
    try
      p token_stream
    with
      Stream.Error msg -> raise (ParseException (loc(), msg))
    | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

let read_file_lines path =
  let channel = open_in path in
  let lines =
    let rec read_lines () =
      try
        let line = input_line channel in
        let line = chop_suffix_opt line "\r" in
        let lines = read_lines () in
        line::lines
      with
        End_of_file -> []
    in
    read_lines ()
  in
  close_in channel;
  lines

let file_loc path =
  let pos = ((Filename.dirname path, Filename.basename path), 1, 1) in
  (pos, pos)

let expand_macros macros text =
  if not (String.contains text '%') then text else
  let n = String.length text in
  let buffer = Buffer.create n in
  let rec iter i =
    if i < n then
    let c = text.[i] in
    let add_char () =
      Buffer.add_char buffer c;
      iter (i + 1)
    in
    if c = '%' then
      let j = String.index_from text (i + 1) '%' in
      if j <= i then begin
      end else begin
        let symbol = String.sub text (i + 1) (j - i - 1) in
        match try_assoc symbol macros with
          None -> add_char ()
        | Some value -> Buffer.add_string buffer value; iter (j + 1)
      end
    else
      add_char ()
  in
  iter 0;
  Buffer.contents buffer

let path_macros = [("VERIFAST", rtdir)]

let expand_path path =
  expand_macros path_macros path

let concat_if_relative path1 path2 =
  if Filename.is_relative path2 then
    concat path1 path2
  else
    path2

(* Returned paths are relative to the directory of [path] *)
let parse_jarspec_file_core path =
  let lines = read_file_lines path in
  let (jarspecs, lines) =
    let rec iter jarspecs lines =
      match lines with
      | line::lines when line = "" ->
        iter jarspecs lines
      | line::lines when Filename.check_suffix line ".jarspec" ->
        iter ((expand_path line)::jarspecs) lines
      | _ ->
        (List.rev jarspecs, lines)
    in
    iter [] lines
  in
  let javaspecs =
    flatmap
      begin fun line ->
        if line = "" then [] else
        if not (Filename.check_suffix line ".javaspec") then
          raise (ParseException (file_loc path, "A .jarspec file must consists of a list of .jarspec file paths followed by a list of .javaspec file paths"))
        else
          [line]
      end
      lines
  in
  (jarspecs, javaspecs)

(* Returned paths are relative to the directory of [path] *)
let parse_jarsrc_file_core path =
  let lines = read_file_lines path in
  let (jars, lines) =
    let rec iter jars lines =
      match lines with
        line::lines when not (startswith line "main-class ") && Filename.check_suffix line ".jar" ->
        iter ((expand_path line)::jars) lines
      | _ ->
        (List.rev jars, lines)
    in
    iter [] lines
  in
  let (javas, lines) =
    let rec iter javas lines =
      match lines with
        line::lines when not (startswith line "main-class ") && Filename.check_suffix line ".java" ->
        iter (line::javas) lines
      | _ ->
        (List.rev javas, lines)
    in
    iter [] lines
  in
  let (provides, lines) =
    let rec iter provides lines =
      match lines with
        line::lines when startswith line "provides " ->
        let provide = String.sub line (String.length "provides ") (String.length line - String.length "provides ") in
        iter (provide::provides) lines
      | _ ->
        (List.rev provides, lines)
    in
    iter [] lines
  in
  let provides =
    match lines with
      [] -> provides
    | [line] when startswith line "main-class " ->
      let mainClass = String.sub line (String.length "main-class ") (String.length line - String.length "main-class ") in
      provides @ ["main_class " ^ mainClass]
    | _ ->
      raise (ParseException (file_loc path, "A .jarsrc file must consists of a list of .jar file paths followed by a list of .java file paths, optionally followed by a line of the form \"main-class mymainpackage.MyMainClass\""))
  in
  (jars, javas, provides)
