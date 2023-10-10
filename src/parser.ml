open Big_int
open Num
open Util
open Stats
open Lexer
open Ast

(* Region: the parser *)

let common_keywords = []

let c_keywords = [
  (* C18 keywords *)
  "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum";
  "extern"; "float"; "for"; "goto"; "if"; "inline"; "int"; "long"; "register"; "restrict"; "return";
  "short"; "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile";
  "while"; "_Alignas"; "_Alignof"; "_Atomic"; "_Bool"; "_Complex"; "_Generic"; "_Imaginary"; "_Noreturn"; "_Static_assert"; "_Thread_local";

  (* C18 punctuators *)
  "["; "]"; "("; ")"; "{"; "}"; "."; "->";
  "++"; "--"; "&"; "*"; "+"; "-"; "~"; "!";
  "/"; "%"; "<<"; ">>"; "<"; ">"; "<="; ">="; "=="; "!="; "^"; "|"; "&&"; "||";
  "?"; ":"; ";"; "...";
  "="; "*="; "/="; "%="; "+="; "-="; "<<="; ">>="; "&="; "^="; "|=";
  ","; "#"; "##";
  "<:"; ":>"; "<%"; "%>"; "%:"; "%:%:";

  (* C18 preprocessing directives *)
  "ifdef"; "ifndef"; "elif"; "endif"; "include"; "define"; "undef"; (* "line"; "error"; *) "pragma";

  (* GNU C extensions *)
  "__always_inline"; "__attribute__"; "__forceinline"; "__inline"; "__inline__"; "__signed__";

  (* The following are macros or typedefs in C but we treat them as keywords *)
  "CHAR_MAX"; "CHAR_MIN"; "INT_MAX"; "INT_MIN"; "LLONG_MAX"; "LLONG_MIN"; "LONG_MAX"; "LONG_MIN"; "SHRT_MAX"; "SHRT_MIN";
  "UCHAR_MAX"; "UINT_MAX"; "UINTPTR_MAX"; "ULLONG_MAX"; "ULONG_MAX"; "USHRT_MAX";
  "assert"; "bool"; "false"; "intptr_t"; "true"; "uintptr_t"; "varargs";

  (* VeriFast keywords *)
  "__int8"; "__int16"; "__int32"; "__int64"; "__int128"; "__minvalue"; "__maxvalue";
(* Note: it's important for soundness that currentCodeFractions, currentThread, and varargs be considered keywords both inside and outside of annotations. *)
  "currentCodeFractions"; "currentThread"; "real" (* "real" really should be a ghost keyword, but it's used in vf__floating_point.h... *)
]

let cxx_keywords = [
  (* C++17 keywords *)
   "alignas"; "alignof"; "asm"; "auto"; "bool"; "break"; "case"; "catch"; "char"; "char16_t"; "char32_t"; "class"; "const"; "constexpr"; "const_cast";
   "continue"; "decltype"; "default"; "delete"; "do"; "double"; "dynamic_cast"; "else"; "enum"; "explicit"; "export"; "extern"; "false"; "float"; "for";
   "friend"; "goto"; "if"; "inline"; "int"; "long"; "mutable"; "namespace"; "new"; "noexcept"; "nullptr"; "operator"; "private"; "protected"; "public";
   "register"; "reinterpret_cast"; "return"; "short"; "signed"; "sizeof"; "static"; "static_assert"; "static_cast"; "struct"; "switch"; "template"; (*"this";*) "thread_local"; "throw";
   "true"; "try"; "typedef"; "typeid"; "typename"; "union"; "unsigned"; "using"; "virtual"; "void"; "volatile"; "wchar_t"; "while";

   (* C++17 punctuators *)
   "{"; "}"; "["; "]"; "#"; "##"; "("; ")";
   "<:"; ":>"; "<%"; "%>"; "%:"; "%:%:"; ";"; ":"; "...";
   "new"; "delete"; "?"; "::"; "."; ".*";
   "+"; "-"; "*"; "/"; "%"; "^"; "&"; "|"; "~";
   "!"; "="; "<"; ">"; "+="; "-="; "*="; "/="; "%=";
   "^="; "&="; "|="; "<<"; ">>"; ">>="; "<<="; "=="; "!=";
   "<="; ">="; "&&"; "||"; "++"; "--"; ","; "->*"; "->";

  (* C++17 preprocessing directives *)
  "include"; "define"; "undef"; (*"line"; "error";*) "pragma"; "ifdef"; "ifndef"; "elif"; "endif";

  (* GNU C++ extensions *)
  "__always_inline"; "__attribute__"; "__forceinline"; "__inline"; "__inline__"; "__signed__";

  (* The following are macros or typedefs in C++ but we treat them as keywords *)
  "CHAR_MAX"; "CHAR_MIN"; "INT_MAX"; "INT_MIN"; "LLONG_MAX"; "LLONG_MIN"; "LONG_MAX"; "LONG_MIN"; "SHRT_MAX"; "SHRT_MIN";
  "UCHAR_MAX"; "UINT_MAX"; "UINTPTR_MAX"; "ULLONG_MAX"; "ULONG_MAX"; "USHRT_MAX";
  "assert"; "intptr_t"; "uintptr_t"; "varargs";

  (* VeriFast keywords *)
  "__int8"; "__int16"; "__int32"; "__int64"; "__int128"; "__minvalue"; "__maxvalue";
(* Note: it's important for soundness that currentCodeFractions, currentThread, and varargs be considered keywords both inside and outside of annotations. *)
  "currentCodeFractions"; "currentThread"; "real" (* "real" really should be a ghost keyword, but it's used in vf__floating_point.h... *)
]

let rust_keywords = [
  "as"; "break"; "const"; "continue"; "crate"; "else"; "enum"; "extern";
  "false"; "fn"; "for"; "if"; "impl"; "in"; "let"; "loop"; "match"; "mod";
  "move"; "mut"; "pub"; "ref"; "return"; "self"; "Self"; "static"; "struct";
  "super"; "trait"; "true"; "type"; "unsafe"; "use"; "where"; "while";

  "async"; "await"; "dyn";

  "abstract"; "become"; "box"; "do"; "final"; "macro"; "override"; "priv";
  "typeof"; "unsized"; "virtual"; "yield";

  "try";

  "+"; "-"; "*"; "/"; "%"; "^"; "&"; "|"; "&&"; "||"; "<<"; ">>"; "+="; "-=";
  "*="; "/="; "%="; "^="; "&="; "|="; "<<="; ">>="; "="; "=="; "!="; ">"; "<";
  ">="; "<="; "@"; "_"; "."; ".."; "..."; "..="; ","; ";"; ":"; "::"; "->";
  "=>"; "#"; "$"; "?"; "~";

  "{"; "}"; "["; "]"; "("; ")";

  "'a" (* this pseudo-keyword is a hack; its presence signals to the lexer that tokens of the form 'abc (i.e. Rust lifetime tokens) are allowed *)
]

let java_keywords = [
  (* JLS6 keywords *)
  "abstract"; "assert"; "boolean"; "break"; "byte"; "case"; "catch"; "char"; "class"; "const";
  "continue"; "default"; "do"; "double"; "else"; "enum"; "extends"; "final"; "finally"; "float";
  "for"; "if"; "goto"; "implements"; "import"; "instanceof"; "int"; "interface"; "long"; "native";
  "new"; "package"; "private"; "protected"; "public"; "return"; "short"; "static"; "strictfp"; "super";
  "switch"; "synchronized"; (*"this";*) "throw"; "throws"; "transient"; "try"; "void"; "volatile"; "while";

  (* JLS6 separators *)
  "("; ")"; "{"; "}"; "["; "]"; ";"; ","; ".";

  (* JLS6 operators *)
  "="; ">"; "<"; "!"; "~"; "?"; ":";
  "=="; "<="; ">="; "!="; "&&"; "||"; "++"; "--";
  "+"; "-"; "*"; "/"; "&"; "|"; "^"; "%"; "<<"; ">>"; ">>>";
  "+="; "-="; "*="; "/="; "&="; "|="; "^="; "%="; "<<="; ">>="; ">>>=";

  (* JLS6 literals *)
  "false"; "null"; "true";

  (* VeriFast keywords *)
(* Note: it's important for soundness that currentThread be considered a keyword both inside and outside of annotations. *)
  "currentThread"; "real" (* "real" really should be a ghost keyword, but it's used in vf__floating_point.h... *)
]

let ghost_keywords = [
  "predicate"; "copredicate"; "requires"; "|->"; "&*&"; "inductive"; "fixpoint";
  "ensures"; "close"; "lemma"; "open"; "emp"; "invariant"; "lemma_auto";
  "_"; "@*/"; "predicate_family"; "predicate_family_instance"; "predicate_ctor"; "leak"; "@";
  "box_class"; "action"; "handle_predicate"; "preserved_by"; "consuming_box_predicate"; "consuming_handle_predicate"; "perform_action"; "nonghost_callers_only";
  "create_box"; "above"; "below"; "and_handle"; "and_fresh_handle"; "create_handle"; "create_fresh_handle"; "dispose_box"; 
  "produce_lemma_function_pointer_chunk"; "duplicate_lemma_function_pointer_chunk"; "produce_function_pointer_chunk";
  "producing_box_predicate"; "producing_handle_predicate"; "producing_fresh_handle_predicate"; "box"; "handle"; "any"; "split_fraction"; "by"; "merge_fractions";
  "unloadable_module"; "decreases"; "forall_"; "import_module"; "require_module"; ".."; "extends"; "permbased";
  "terminates"; "abstract_type"; "fixpoint_auto"; "typeid"; "activating"; "truncating"; "typedef"
]

exception CompilationError of string

let file_specs path =
  begin
    if Filename.check_suffix (Filename.basename path) ".c" then CLang, None
    else if Filename.check_suffix (Filename.basename path) ".cpp" then CLang, Some (Cxx)
    else if Filename.check_suffix (Filename.basename path) ".jarsrc" then Java, None
    else if Filename.check_suffix (Filename.basename path) ".jarspec" then Java, None
    else if Filename.check_suffix (Filename.basename path) ".java" then Java, None
    else if Filename.check_suffix (Filename.basename path) ".javaspec" then Java, None
    else if Filename.check_suffix (Filename.basename path) ".scala" then Java, None
    else if Filename.check_suffix (Filename.basename path) ".h" then CLang, None
    else raise (CompilationError ("unknown extension: " ^ (Filename.basename path)))
  end
let file_type path =
  let f, _ = file_specs path in
  f
let lang_dialect path =
  let _, d = file_specs path in
  d
let opt p = function%parser [ p as v ] -> Some v | [ ] -> None
let rec comma_rep p = function%parser [ (_, Kwd ","); p as v; [%l vs = comma_rep p] ] -> v::vs | [ ] -> []
let rep_comma p = function%parser [ p as v; [%l vs = comma_rep p] ] -> v::vs | [ ] -> []
let rec rep p = function%parser [ p as v; [%l vs = rep p] ] -> v::vs | [ ] -> []
let rec adjacent_locs l0 l1 =
  match l0, l1 with
    MacroExpansion (lcall1, lbody1), MacroExpansion (lcall2, lbody2) when lcall1 == lcall2 ->
    adjacent_locs lbody1 lbody2
  | _ ->
    let (_, sp0) = root_caller_token l0 in
    let (sp1, _) = root_caller_token l1 in
    sp0 = sp1
let parse_angle_brackets l0 p =
  function%parser [ (l1, Kwd "<"); p as v; (_, Kwd ">") ] when adjacent_locs l0 l1 -> v

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
| TerminatesClause of loc

let next_body_rank =
  let counter = ref 0 in
  fun () -> incr counter; !counter

(* A toy Scala parser. *)
module Scala = struct

  let keywords = [
    "def"; "var"; "class"; "object"; "."; "new"; "null"; "package"; "import";
    "+"; "="; "("; ")"; ":"; "{"; "}"; "["; "]"; "/*@"; "@*/"; "=="; "="; ";"; "true"; "false"; "assert"
  ]

  let rec
    parse_decl = function%parser
      [ (l, Kwd "object"); (_, Ident cn); (_, Kwd "{"); [%l ms = rep parse_method]; (_, Kwd "}") ] ->
      Class (l, false, FinalClass, cn, ms, [], [], ("Object", []), [], [], [])
  and
    parse_method = function%parser
      [ (l, Kwd "def"); (_, Ident mn); parse_paramlist as ps; parse_type_ann as t; parse_contract as co; (_, Kwd "=");(_, Kwd "{"); [%l ss = rep parse_stmt]; (closeBraceLoc, Kwd "}") ] ->
      let rt = match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t in
      Meth (l, Real, rt, mn, ps, Some co, Some ((ss, closeBraceLoc), next_body_rank ()), Static, Public, false, [])
  and
    parse_paramlist = function%parser
      [ (_, Kwd "("); [%l ps = rep_comma parse_param]; (_, Kwd ")") ] -> ps
  and
    parse_param = function%parser
      [ (_, Ident x); parse_type_ann as t ] -> (t, x)
  and
    parse_type_ann: (loc * token) Stream.t -> type_expr = function%parser
      [ (_, Kwd ":"); parse_type as t ] -> t
  and
    parse_type = function%parser
      [ (l, Ident tn); parse_targlist as targs ] ->
      begin
        match (tn, targs) with
          ("Unit", []) -> ManifestTypeExpr (l, Void)
        | ("Int", []) -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 2))
        | ("Array", [t]) -> ArrayTypeExpr (l, t)
        | (_, []) -> IdentTypeExpr (l, None, tn)
        | _ -> raise (ParseException (l, "Type arguments are not supported."))
      end
  and
    parse_targlist = function%parser
      [ (_, Kwd "["); [%l ts = rep_comma parse_type]; (_, Kwd "]") ] -> ts
    | [ ] -> []
  and
    parse_contract = function%parser
      [ (_, Kwd "/*@"); (_, Kwd "requires"); parse_asn as pre; (_, Kwd "@*/");
         (_, Kwd "/*@"); (_, Kwd "ensures"); parse_asn as post; (_, Kwd "@*/") ] -> (pre, post, [], false)
  and
    parse_asn = function%parser
      [ (_, Kwd "("); parse_asn as a; (_, Kwd ")") ] -> a
    | [ parse_expr as e ] -> e
  and
    parse_primary_expr = function%parser
      [ (l, Kwd "true") ] -> True l
    | [ (l, Kwd "false") ] -> False l
    | [ (l, Int (n, dec, usuffix, lsuffix, _)) ] -> IntLit (l, n, dec, usuffix, lsuffix)
    | [ (l, Ident x) ] -> Var (l, x)
  and
    parse_add_expr = function%parser
      [ parse_primary_expr as e0; [%l e = parse_add_expr_rest e0] ] -> e
  and
    parse_add_expr_rest e0 = function%parser
      [ (l, Kwd "+"); parse_primary_expr as e1; [%l e = parse_add_expr_rest (Operation (l, Add, [e0; e1]))] ] -> e
    | [ ] -> e0
  and
    parse_rel_expr = function%parser
      [ parse_add_expr as e0; [%l e = parse_rel_expr_rest e0] ] -> e
  and
    parse_rel_expr_rest e0 = function%parser
      [ (l, Kwd "=="); parse_add_expr as e1; [%l e = parse_rel_expr_rest (Operation (l, Eq, [e0; e1]))] ] -> e
    | [ ] -> e0
  and
    parse_expr stream = parse_rel_expr stream
  and
    parse_stmt = function%parser
      [ (l, Kwd "var"); (_, Ident x); parse_type_ann as t; (_, Kwd "="); parse_expr as e; (_, Kwd ";") ] -> DeclStmt (l, [l, t, x, Some(e), (ref false, ref None)])
    | [ (l, Kwd "assert"); parse_asn as a; (_, Kwd ";") ] -> Assert (l, a)

end

(* The C/Java parser.
   The difference is in the scanner: when parsing a C file, the scanner treats "class" like an identifier, not a keyword.
   And Kwd "class" does not match Ident "class".
   *)

let pat_of_expr e =
  match e with
    CallExpr (l, g, [], [], pats, Static) when List.exists (function LitPat _ -> false | _ -> true) pats ->
    CtorPat (l, g, pats)
  | _ -> LitPat e

type modifier = StaticModifier | FinalModifier | AbstractModifier | VisibilityModifier of visibility

(* Ugly hack *)
let typedefs: (string, unit) Hashtbl.t = Hashtbl.create 64
let typedefs_enabled = ref true
let set_typedefs_enabled b =
  let old_typedefs_enabled = !typedefs_enabled in
  typedefs_enabled := b;
  old_typedefs_enabled
let register_typedef g = if not (Hashtbl.mem typedefs g) then Hashtbl.add typedefs g ()
let is_typedef g = Hashtbl.mem typedefs g && !typedefs_enabled
let typedef_scopes = ref []
let push_typedef_scope () =
  typedef_scopes := ref []::!typedef_scopes
let register_varname x =
  if Hashtbl.mem typedefs x then begin
    match !typedef_scopes with
      scope::_ ->
      scope := x::!scope;
      Hashtbl.remove typedefs x
    | _ ->
      ()
  end
let pop_typedef_scope () =
  let scope::scopes = !typedef_scopes in
  List.iter register_typedef !scope;
  typedef_scopes := scopes

module type PARSER_ARGS = sig
  val language: language
  val enforce_annotations: bool
  val data_model: data_model option
end

let decompose_data_model data_model_opt =
  match data_model_opt with
    Some {int_width; long_width; ptr_width} -> LitWidth int_width, LitWidth long_width, LitWidth ptr_width
  | None -> IntWidth, LongWidth, PtrWidth

module Parser(ParserArgs: PARSER_ARGS) = struct

open ParserArgs

let int_width, long_width, ptr_width = decompose_data_model data_model

let intType = Int (Signed, IntRank)
let longType = Int (Signed, LongRank)

let get_unnamed_param_name =
  let counter = ref 0 in
  fun () ->
    let n = !counter in
    incr counter;
    "__unnamed_param" ^ string_of_int n

let rec parse_decls ?inGhostHeader =
  if match inGhostHeader with None -> false | Some b -> b then
    parse_pure_decls
  else
    parse_decls_core
and
  parse_decls_core = function%parser
  [ (_, Kwd "/*@"); parse_pure_decls as ds; (_, Kwd "@*/"); parse_decls_core as ds' ] -> ds @ ds'
| [ [%l _d = opt (function%parser [ (_, Kwd "public") ] -> ()) ];
    [%l abstract = (function%parser [ (_, Kwd "abstract") ] -> true | [ ] -> false)]; 
    [%l final = (function%parser [ (_, Kwd "final") ] -> FinalClass | [ ] -> ExtensibleClass)];
    [%l ds = begin function%parser
    | [ (l, Kwd "class"); (_, Ident s); type_params_parse as tparams;
        [%l super = parse_super_class l]; parse_interfaces as il; [%l mem = parse_java_members s tparams]; parse_decls_core as ds ]
      -> Class (l, abstract, final, s, methods s mem, fields mem, constr mem, super, tparams, il, instance_preds mem)::ds
    | [ (l, Kwd "interface"); (_, Ident cn); type_params_parse as tparams;
        parse_extended_interfaces as il; [%l mem = parse_java_members cn tparams]; parse_decls_core as ds ]
      -> Interface (l, cn, il, fields mem, methods cn mem, tparams, instance_preds mem)::ds
    | [ parse_decl as d; parse_decls_core as ds ] -> d@ds
    | [ (_, Kwd ";"); parse_decls_core as ds ] -> ds
    | [ ] -> []
     end]
  ] -> ds
and parse_qualified_type loc = function%parser
  [ parse_type as t ] -> 
    match t with 
      IdentTypeExpr(l, p, n) -> ((match p with Some(s) -> s ^ "." ^ n | None -> n), []) 
      | ConstructedTypeExpr(l, n, targs) -> (n, targs)
      | _ -> raise (ParseException (loc, "Invalid type"))
  
and
  parse_super_class loc = function%parser
    [ (l, Kwd "extends"); [%l (s, targs) = parse_qualified_type l] ] -> (s, targs)
  | [ ] -> ("java.lang.Object", [])
and
  parse_interfaces = function%parser
| [
    (l, Kwd "implements"); 
    [%l is = rep_comma (function%parser 
    | [ 
        [%l i = parse_qualified_type l]; 
        [%l e = function%parser [ ] -> i]
      ] -> e)
    ];
    (_, Kwd "{") 
  ] -> is
  | [ (_, Kwd "{") ]-> []
and
  parse_extended_interfaces = function%parser
| [ (l, Kwd "extends"); 
    [%l is = rep_comma (function%parser 
    | [ [%l i = parse_qualified_type l]; 
        [%l e = function%parser
        | [ ] -> i
        ]
      ] -> e)
    ]; 
    (_, Kwd "{") ] -> is
| [ (_, Kwd "{") ] -> []
and
  methods cn m=
  match m with
    MethMember (Meth (l, gh, t, n, ps, co, ss, s, v, abstract, tparams))::ms -> Meth (l, gh, t, n, ps, co, ss, s, v, abstract, tparams)::(methods cn ms)
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
  parse_visibility = function%parser
| [ (_, Kwd "public") ] -> Public
| [ (_, Kwd "private") ] -> Private
| [ (_, Kwd "protected") ] -> Protected
| [ ] -> Package
and
  parse_java_members cn ctparams = function%parser
| [ (_, Kwd "}") ] -> []
| [ (_, Kwd "/*@"); [%l mems1 = parse_ghost_java_members cn]; [%l mems2 = parse_java_members cn ctparams] ] -> mems1 @ mems2
| [ [%l m = parse_java_member cn ctparams]; [%l mr = parse_java_members cn ctparams] ] -> m::mr
and
  parse_ghost_java_members cn = function%parser
  [ (_, Kwd "@*/") ] -> []
| [ [%l m = parse_ghost_java_member cn]; [%l mems = parse_ghost_java_members cn] ] -> m::mems
and
  parse_ghost_java_member cn = function%parser
| [ parse_visibility as vis; 
    [%l m = begin function%parser
    | [ (l, Kwd "predicate"); 
        (_, Ident g); 
        parse_paramlist as ps;
        [%l 
          body = begin function%parser
          | [ (_, Kwd "="); parse_asn as p ] -> Some p
          | [ ] -> None
          end
        ];
        (_, Kwd ";") 
      ] -> PredMember(InstancePredDecl (l, g, ps, body))
    | [ (l, Kwd "lemma"); 
        parse_return_type as t; 
        (l, Ident x); 
        [%l (ps, co, ss) = parse_method_rest l] 
      ] -> 
        let ps = (IdentTypeExpr (l, None, cn), "this")::ps in
        MethMember(Meth (l, Ghost, t, x, ps, co, ss, Instance, vis, false, []))
    | [ [%l binding = (function%parser 
        | [ (_, Kwd "static") ] -> Static 
        | [ ] -> Instance)
        ]; 
        parse_type as t; 
        (l, Ident x); 
        (_, Kwd ";") 
      ] -> FieldMember [Field (l, Ghost, t, x, binding, vis, false, None)]
    end
    ]
  ] -> m
and
  parse_thrown l = function%parser 
| [ parse_type as tp; 
    [%l 
    epost = begin function%parser
    | [ (_, Kwd "/*@"); (_, Kwd "ensures"); parse_asn as epost; (_, Kwd ";"); (_, Kwd "@*/") ] -> Some epost
    | [ ] -> None
    end
    ]
  ] -> (tp, epost)
and
  parse_throws_clause = function%parser
  [ (l, Kwd "throws"); [%l epost = rep_comma (parse_thrown l)] ] -> epost
and
  parse_array_dims t = function%parser
| [ (l, Kwd "["); (_, Kwd "]"); [%l t = parse_array_dims (ArrayTypeExpr (l, t))] ] -> t
| [ ] -> t
and 
  id x = function%parser [ ] -> x
and 
  parse_java_modifier = function%parser [ (_, Kwd "public") ] -> VisibilityModifier(Public) | [ (_, Kwd "protected") ] -> VisibilityModifier(Protected) | [ (_, Kwd "private") ] -> VisibilityModifier(Private) | [ (_, Kwd "static") ] -> StaticModifier | [ (_, Kwd "final") ] -> FinalModifier | [ (_, Kwd "abstract") ] -> AbstractModifier
and
  parse_java_member cn classTparams = function%parser
| [ [%l modifiers = rep parse_java_modifier];
    [%l binding = (fun _ -> if List.mem StaticModifier modifiers then Static else Instance)];
    [%l final = (fun _ -> List.mem FinalModifier modifiers)];
    [%l abstract = (fun _ -> List.mem AbstractModifier modifiers)];
    [%l vis = (fun _ -> (match (try_find (function VisibilityModifier(_) -> true | _ -> false) modifiers) with None -> Package | Some(VisibilityModifier(vis)) -> vis))];
    parse_type_params_general as tparams;
    parse_return_type as t;
    [%l 
      member = function%parser
      | [ (l, Ident x);
          [%l 
            member = function%parser
            | [ [%l (ps, co, ss) = parse_method_rest l] ] ->
              let this = if classTparams <> [] then ConstructedTypeExpr(l,cn,List.map (fun tparam -> IdentTypeExpr(l, None, tparam) ) classTparams) else IdentTypeExpr (l, None, cn) in
              let ps = 
                if binding = Instance then (this, "this")::ps 
                else ps 
              in
              MethMember (Meth (l, Real, t, x, ps, co, ss, binding, vis, abstract, tparams))
            | [ [%l t = id (match t with None -> raise (ParseException (l, "A field cannot be void.")) | Some(t) -> t)];
                [%l tx = parse_array_braces t];
                [%l init = opt (function%parser [ (_, Kwd "="); [%l e = parse_declaration_rhs tx] ] -> e)];
                [%l ds = comma_rep (parse_declarator t)];
                (_, Kwd ";")
              ] ->
              let fds =
              ((l, tx, x, init, (ref false, ref None))::ds) |> List.map begin fun (l, tx, x, init, _) ->
                Field (l, Real, tx, x, binding, vis, final, init)
              end
              in
              FieldMember fds
          ]
        ] -> member
      | [ [%l (ps, co, ss) = parse_method_rest (match t with Some t -> type_expr_loc t | None -> dummy_loc)] ] ->
        let l =
          match t with
          | None -> raise (Stream.Error "Keyword 'void' cannot be followed by a parameter list.")
          | Some (IdentTypeExpr (l, None, x)) -> if x = cn then l else raise (ParseException (l, "Constructor name does not match class name."))
          | Some t -> raise (ParseException (type_expr_loc t, "Constructor name expected."))
          in
          if binding = Static then raise (ParseException (l, "A constructor cannot be static."));
          if final then raise (ParseException (l, "A constructor cannot be final."));
          ConsMember (Cons (l, ps, co, ss, vis))
    ]
  ] -> member
and parse_array_init_rest = function%parser
| [ (_, Kwd ","); 
    [%l es = opt (function%parser [ parse_expr as e; parse_array_init_rest as es ] -> e :: es)]
  ] -> (match es with None -> [] | Some(es) -> es)
| [ ] -> []
and parse_array_init = function%parser
| [ (_, Kwd ","); 
    (_, Kwd "}") 
  ] -> []
| [ (_, Kwd "}") ] -> []
| [ parse_expr as e; parse_array_init_rest as es; (_, Kwd "}") ] -> e :: es
and parse_declaration_rhs te = function%parser
| [ (linit, Kwd "{"); 
    parse_array_init as es 
  ] ->
  (match te with ArrayTypeExpr (_, elem_te) when language = Java -> NewArrayWithInitializer (linit, elem_te, es) | _ -> InitializerList (linit, es))
| [ parse_expr as e ] -> e
and
  parse_declarator0 = function%parser
| [ (l, Kwd "(");
    [%l 
    f = begin function%parser
    | [ parse_param as p; 
        [%l ps = comma_rep parse_param]; 
        (_, Kwd ")") 
      ] -> fun t ->
       let ps = List.filter filter_void_params (p::ps) in
       (FuncTypeExpr (l, t, ps), None)
    | [ (_, Kwd ")") ] -> fun t -> (FuncTypeExpr (l, t, []), None)
    | [ parse_declarator0 as f; 
        (_, Kwd ")") 
      ] -> f
    end
    ];
    [%l f = parse_declarator_suffix f]
  ] -> f
| [ (l, Kwd "*"); 
    parse_declarator0 as f 
  ] -> fun t -> f (PtrTypeExpr (l, t))
| [ [%l x = opt (function%parser [ (l, Ident x) ] -> (l, x))];
    [%l f = parse_declarator_suffix (fun t -> (t, x))] 
  ] -> f
and
  parse_declarator_suffix f = function%parser
| [ (l, Kwd "["); 
    [%l 
    f = begin function%parser
    | [ (_, Kwd "]") ] -> fun t -> f (ArrayTypeExpr (l, t))
    | [ (lsize, Int (size, _, _, _, _)); 
        (_, Kwd "]") 
      ] ->
      if sign_big_int size <= 0 then raise (ParseException (lsize, "Array must have size > 0."));
      fun t -> f (StaticArrayTypeExpr (l, t, int_of_big_int size))
    end
    ]; 
    [%l f = parse_declarator_suffix f]
  ] -> f
| [ (l, Kwd "(");
    [%l ps = rep_comma parse_param]; 
    (_, Kwd ")"); 
    [%l f = parse_declarator_suffix (fun t -> f (FuncTypeExpr (l, t, List.filter filter_void_params ps)))]
  ] -> f
| [ ] -> f
and
  parse_declarator t = function%parser
| [ [%l t = parse_type_suffix t];
    (l, Ident x);
    [%l tx = parse_array_braces t];
    [%l init = opt (function%parser [ (_, Kwd "="); [%l e = parse_declaration_rhs tx] ] -> e)];
  ] ->
  let tx =
    match tx, init with
      ArrayTypeExpr (l, elemTp), Some (InitializerList (_, es)) when language = CLang ->
      StaticArrayTypeExpr (l, elemTp, List.length es)
    | _ -> tx
  in
  register_varname x;
  (l, tx, x, init, (ref false, ref None))
and
  parse_method_rest l = function%parser
  [ parse_paramlist as ps;
    [%l epost = opt parse_throws_clause];
    [%l 
    (ss, co) = function%parser
    | [ (_, Kwd ";"); [%l spec = opt parse_spec] ] -> (None, spec)
    | [ [%l spec = opt parse_spec]; (l, Kwd "{"); parse_stmts as ss; (closeBraceLoc, Kwd "}") ] -> (Some ((ss, closeBraceLoc), next_body_rank ()), spec)
    ]
  ] ->
    let contract =
      let epost = match epost with None -> [] | Some(epost) -> epost in
      match co with
      | Some(pre, post, terminates) -> 
        let epost = List.map (fun (tp, e) -> 
          (tp, match e with 
            None -> raise (ParseException (l, "If you give a method a contract, you must also give ensures clauses for the thrown expceptions.")) | 
            Some(e) -> e)) epost 
        in
        Some(pre, post, epost, terminates)
      | None -> 
        if enforce_annotations then None else
        begin
         let pre = ExprAsn(l, False(l)) in
         let post = ExprAsn(l, True(l)) in
         let epost = List.map (fun (tp, e) -> (tp, match e with None -> ExprAsn(l, True(l)) | Some(e) -> e)) epost in
         Some (pre, post, epost, false)
        end
    in
    (ps, contract, ss)
and
  parse_functype_paramlists = function%parser
| [ parse_paramlist as ps1; [%l ps2 = opt parse_paramlist] ] -> (match ps2 with None -> ([], ps1) | Some ps2 -> (ps1, ps2))
and
  (** Parses
   * /*@<ttparams>(tparams)@*/(params) where
   * <ttparams> and (tparams) and /*@<ttparams>(tparams)@*/ are optional
   *)
  parse_functypedecl_paramlist_in_real_context = function%parser
| [ (_, Kwd "/*@");
    [%l functiontypetypeparams = opt parse_type_params_free];
    [%l functiontypeparams = opt parse_paramlist];
    (_, Kwd "@*/");
    parse_paramlist as params
  ] ->
    let noneToEmptyList value = 
      match value with 
        None -> []
        | Some x -> x
    in
    (noneToEmptyList functiontypetypeparams, noneToEmptyList functiontypeparams, params)
| [ parse_paramlist as params ] -> ([], [], params)
and
  parse_ignore_inline = function%parser
| [ (l, Kwd "inline") ] -> ()
| [ (l, Kwd "__inline") ] -> ()
| [ (l, Kwd "__inline__") ] -> ()
| [ (l, Kwd "__forceinline") ] -> ()
| [ (l, Kwd "__always_inline") ] -> ()
| [ ] -> ()
and
  parse_static_visibility = function%parser
| [ (l, Kwd "static") ] -> Private
| [ ] -> Public
and
  parse_enum_body = function%parser
| [ (_, Kwd "{");
    [%l 
    elems = rep_comma (function%parser 
    | [ (_, Ident e); 
        [%l 
        init = opt (function%parser 
        | [ (_, Kwd "="); 
            parse_expr as e 
          ] -> e) 
        ]
      ] -> (e, init))
    ];
    (_, Kwd "}")
  ] -> elems
and
  parse_decl = function%parser
| [ (l, Kwd "struct"); 
    (_, Ident s); 
    [%l
    d = function%parser
    | [ parse_fields as fs; 
        [%l
        attrs = begin function%parser
        | [ (_, Kwd "__attribute__"); 
            parse_struct_attrs as res; 
          ] -> res
        | [ ] -> [] 
        end
        ];
        (_, Kwd ";") 
      ] -> Struct (l, s, Some ([], fs, [], false), attrs)
    | [ (_, Kwd ";") ] -> Struct (l, s, None, [])
    | [ [%l t = parse_type_suffix (StructTypeExpr (l, Some s, None, []))]; 
        [%l d = parse_func_rest Regular (Some t)]
      ] -> d
    ]
  ] -> check_function_for_contract d
| [ (l, Kwd "union"); 
    (_, Ident u); 
    [%l 
    d = function%parser
    | [ parse_fields as fs; 
      (_, Kwd ";") 
      ] -> Union (l, u, Some fs)
    | [ (_, Kwd ";") ] -> Union (l, u, None)
    | [ [%l t = parse_type_suffix (UnionTypeExpr (l, Some u, None))]; 
        [%l d = parse_func_rest Regular (Some t)] 
      ] -> d
    ]
  ] -> check_function_for_contract d
| [ (l, Kwd "typedef");
    [%l () = (fun _ -> push_typedef_scope ())];
    parse_return_type as rt;
    [%l
    g, ds = begin function%parser
    | [ (_, Ident g);
        [%l 
        ds = begin function%parser
        | [ [%l (tparams, ftps, ps) = parse_functypedecl_paramlist_in_real_context];
            (_, Kwd ";");
            [%l spec = opt parse_spec]
          ] ->
          let contract = check_for_contract spec l "Function type declaration should have contract." (fun (pre, post) -> (pre, post, false)) in
          [FuncTypeDecl (l, Real, rt, g, tparams, ftps, ps, contract)]
        | [ (_, Kwd ";") ] ->
          begin match rt with
          | None -> raise (ParseException (l, "Void not allowed here."))
          | Some (EnumTypeExpr (le, en_opt, Some body)) ->
            let en = match en_opt with None -> g | Some en -> en in
            [EnumDecl (l, en, body); TypedefDecl (l, EnumTypeExpr (le, Some en, None), g)]
          | Some (StructTypeExpr (ls, s_opt, Some fs, attrs)) ->
            let s = match s_opt with None -> g | Some s -> s in
            [Struct (l, s, Some ([], fs, [], false), attrs); TypedefDecl (l, StructTypeExpr (ls, Some s, None, attrs), g)]
          | Some (UnionTypeExpr (ls, u_opt, Some fs)) ->
            let u = match u_opt with None -> g | Some u -> u in
            [Union (l, u, Some fs); TypedefDecl (l, UnionTypeExpr (ls, Some u, None), g)]
          | Some PtrTypeExpr (lp, (StructTypeExpr (ls, s_opt, Some fs, attrs))) ->
            let s = match s_opt with None -> g | Some s -> s in
            [Struct (l, s, Some ([], fs, [], false), attrs); TypedefDecl (l, PtrTypeExpr (lp, StructTypeExpr (ls, Some s, None, attrs)), g)]
          | Some te ->
            [TypedefDecl (l, te, g)]
          end
        end
        ]
      ] -> g, ds
    | [ (_, Kwd "("); 
        (lp, Kwd "*"); 
        (lg, Ident g); 
        (_, Kwd ")");
        [%l (tparams, ftps, ps) = parse_functypedecl_paramlist_in_real_context];
        (_, Kwd ";");
        [%l spec = opt parse_spec]
      ] -> 
      let contract = check_for_contract spec l "Function type declaration should have contract." (fun (pre, post) -> (pre, post, false)) in
      g, [FuncTypeDecl (l, Real, rt, g, tparams, ftps, ps, contract); TypedefDecl (l, ManifestTypeExpr (lp, PtrType (FuncType g)), g)]
    end
    ]
  ] -> pop_typedef_scope (); register_typedef g; ds
| [ (_, Kwd "enum"); 
    (l, Ident n); 
    [%l
    d = function%parser
    | [ parse_enum_body as elems; 
        (_, Kwd ";"); 
      ] -> EnumDecl(l, n, elems)
    | [ [%l t = parse_type_suffix (EnumTypeExpr (l, Some n, None))]; 
        [%l d = parse_func_rest Regular (Some t)] 
      ] -> d
    ]
  ] -> check_function_for_contract d
| [ (_, Kwd "static"); 
    parse_ignore_inline as _d; 
    parse_return_type as t; 
    [%l d = parse_func_rest Regular t]
  ] -> check_function_for_contract d
| [ (_, Kwd "extern"); 
    parse_return_type as t; 
    [%l d = parse_func_rest Regular t]
  ] -> check_function_for_contract d
| [ (_, Kwd "_Noreturn"); 
    parse_static_visibility as _d; 
    parse_ignore_inline as _d; 
    parse_return_type as t; 
    [%l d = parse_func_rest Regular t]
  ] ->
  let ds = check_function_for_contract d in
  begin match ds with
    [Func (l, k, tparams, t, g, ps, gc, ft, Some (pre, post), terminates, ss, _, _)] ->
    begin match pre, post with
      ExprAsn (_, False _), _ | False _, _ | _, False _ -> ()
    | _ -> raise (ParseException (l, "Function marked 'noreturn' must declare 'ensures false'."))
    end
  | _ -> ()
  end;
  ds
| [ parse_return_type as t; 
    [%l d = parse_func_rest Regular t] 
  ] -> check_function_for_contract d
and check_for_contract: 'a. 'a option -> loc -> string -> (asn * asn -> 'a) -> 'a = fun contract l m f ->
  match contract with
    | Some spec -> spec 
    | None -> 
      if enforce_annotations then 
        raise (ParseException (l, m)) 
      else
        f (ExprAsn(l, False(l)), ExprAsn(l, True(l)))

and check_function_for_contract d =
  match d with
  | Func(l, k, tparams, t, g, ps, gc, ft, contract, terminates, ss, virt, overrides) ->
    let contract = check_for_contract contract l "Function declaration should have a contract." (fun co -> co) in
    [Func(l, k, tparams, t, g, ps, gc, ft, Some contract, terminates, ss, virt, overrides)]
  | _ -> [d]
and
  parse_pure_decls = function%parser
| [ parse_pure_decl as ds0; 
    parse_pure_decls as ds 
  ] -> ds0 @ ds
| [ ] -> []
and
  parse_index_list = function%parser
| [ (_, Kwd "("); 
    [%l
    is = rep_comma (function%parser 
    | [ (l, Ident i); 
        [%l 
        e = function%parser
        | [ (_, Kwd ".");
            (_, Kwd "class")
          ] -> (l, i)
        | [ ]-> (l, i) 
        ]
      ] -> e
    )
    ]; 
    (_, Kwd ")") 
  ] -> is
and
  parse_type_params l = function%parser
| [ [%l xs = parse_angle_brackets l (rep_comma (function%parser [ (_, Ident x) ] -> x))] ] -> xs
| [ ] -> []
and
  parse_pred_body = function%parser
| [ (_, Kwd "="); 
  parse_asn as p 
  ] -> p
and
  parse_pred_paramlist = function%parser
| [ (_, Kwd "("); 
    [%l ps = rep_comma parse_param];
    [%l
    (ps, inputParamCount) = (function%parser 
    | [ (_, Kwd ";"); 
        [%l ps' = rep_comma parse_param]
      ] -> (ps @ ps', Some (List.length ps)) 
    | [ ] -> (ps, None)
    )
    ]; 
    (_, Kwd ")")
  ] -> (ps, inputParamCount)
and
  parse_predicate_decl l (inductiveness: inductiveness) = function%parser 
| [ (li, Ident g); 
    [%l tparams = parse_type_params li]; 
    [%l () = (fun _ -> push_typedef_scope ())];
    [%l (ps, inputParamCount) = parse_pred_paramlist];
    [%l body = opt parse_pred_body];
    (_, Kwd ";");
  ] ->
  pop_typedef_scope ();
  [PredFamilyDecl (l, g, tparams, 0, List.map (fun (t, p) -> t) ps, inputParamCount, inductiveness)] @
  (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
and
  parse_pure_decl = function%parser
| [ (l, Kwd "inductive"); 
    (li, Ident i); 
    [%l tparams = parse_type_params li]; 
    (_, Kwd "="); 
    [%l
    cs = (function%parser 
    | [ parse_ctors as cs ] -> cs 
    | [ parse_ctors_suffix as cs ] -> cs
    )
    ]; 
    (_, Kwd ";") 
  ] -> [Inductive (l, i, tparams, cs)]
| [ (l, Kwd "predicate"); 
    [%l result = parse_predicate_decl l Inductiveness_Inductive] 
  ] -> result
| [ (l, Kwd "copredicate"); 
    [%l result = parse_predicate_decl l Inductiveness_CoInductive] 
  ] -> result
| [ (l, Kwd "predicate_family"); 
    (_, Ident g); 
    parse_paramlist as is; 
    [%l (ps, inputParamCount) = parse_pred_paramlist]; 
    (_, Kwd ";") 
  ] -> [PredFamilyDecl (l, g, [], List.length is, List.map (fun (t, p) -> t) ps, inputParamCount, Inductiveness_Inductive)]
| [ (l, Kwd "predicate_family_instance"); 
    (_, Ident g); 
    parse_index_list as is; 
    [%l () = (fun _ -> push_typedef_scope ())]; 
    parse_paramlist as ps;
    parse_pred_body as p; 
    (_, Kwd ";") 
  ] -> pop_typedef_scope (); [PredFamilyInstanceDecl (l, g, [], is, ps, p)]
| [ (l, Kwd "predicate_ctor"); 
    (_, Ident g); 
    [%l () = (fun _ -> push_typedef_scope ())]; 
    parse_paramlist as ps1; 
    [%l (ps2, inputParamCount) = parse_pred_paramlist];
    parse_pred_body as p; 
    (_, Kwd ";") 
  ] -> pop_typedef_scope (); [PredCtorDecl (l, g, ps1, ps2, inputParamCount, p)]
| [ (l, Kwd "lemma"); 
    parse_return_type as t; 
    [%l d = parse_func_rest (Lemma(false, None)) t] 
  ] -> [d]
| [ (l, Kwd "lemma_auto"); 
    [%l
    trigger = opt (function%parser 
    | [ (_, Kwd "("); 
      parse_expr as e; 
      (_, Kwd ")") 
      ] -> e
    )
    ]; 
    parse_return_type as t; 
    [%l d = parse_func_rest (Lemma(true, trigger)) t] 
  ] -> [d]
| [ (l, Kwd "box_class"); 
    (_, Ident bcn); 
    [%l () = (fun _ -> push_typedef_scope ())]; 
    parse_paramlist as ps;
    (_, Kwd "{"); 
    (_, Kwd "invariant"); 
    parse_asn as inv; 
    (_, Kwd ";");
    parse_action_decls as ads; 
    parse_handle_pred_decls as hpds; 
    (_, Kwd "}") 
  ] -> pop_typedef_scope (); [BoxClassDecl (l, bcn, ps, inv, ads, hpds)]
| [ (l, Kwd "typedef"); 
    (_, Kwd "lemma"); 
    parse_return_type as rt; 
    (li, Ident g); 
    [%l tps = parse_type_params li];
    [%l (ftps, ps) = parse_functype_paramlists]; 
    (_, Kwd ";"); 
    [%l (pre, post, terminates) = parse_spec] 
  ] -> [FuncTypeDecl (l, Ghost, rt, g, tps, ftps, ps, (pre, post, terminates))]
| [ (l, Kwd "unloadable_module"); 
    (_, Kwd ";") 
  ] -> [UnloadableModuleDecl l]
| [ (l, Kwd "import_module"); 
    (_, Ident g); 
    (lx, Kwd ";") 
  ] -> [ImportModuleDecl (l, g)]
| [ (l, Kwd "require_module"); 
    (_, Ident g); 
    (lx, Kwd ";") 
  ] -> [RequireModuleDecl (l, g)]
| [ (l, Kwd "abstract_type"); 
    (_, Ident t); 
    (_, Kwd ";") 
  ] -> [AbstractTypeDecl (l, t)]
| [ (l, Kwd ("fixpoint"|"fixpoint_auto" as kwd)); 
    parse_return_type as rt; 
    (lg, Ident g); 
    parse_type_params_general as tparams;
    [%l () = (fun _ -> push_typedef_scope ())];
    parse_paramlist as ps;
    [%l
    decreases = begin function%parser
    | [ (_, Kwd "decreases"); 
        parse_expr as e; 
        (_, Kwd ";") 
      ] -> Some e
    | [ ] -> None
    end
    ];
    [%l
    body = begin function%parser
    | [ (_, Kwd "{"); 
        parse_stmts as ss; 
        (closeBraceLoc, Kwd "}") 
      ] -> Some (ss, closeBraceLoc)
    | [ (_, Kwd ";") ] -> None
    end
    ]
  ] ->
    pop_typedef_scope ();
    let rec refers_to_g state e =
      match e with
        CallExpr (_, g', _, _, _, _) when g' = g -> true
      | Var (_, g') when g' = g -> true
      | _ -> expr_fold_open refers_to_g state e
    in
    begin match body with
      Some ([ReturnStmt (_, Some bodyExpr)], _) when refers_to_g false bodyExpr ->
      let rt =
        match rt with
          None -> raise (ParseException (l, "The return type of a fixpoint function must not be 'void'."))
        | Some rt -> rt
      in
      let gdef = g ^ "__def" in
      let iargs = g ^ "__args" in
      let iargsType = ConstructedTypeExpr (l, iargs, List.map (fun x -> IdentTypeExpr (l, None, x)) tparams) in
      let g_uncurry = g ^ "__uncurry" in
      let gdef_curried = g ^ "__def_curried" in
      let measure =
        match decreases, bodyExpr with
          Some e, _ -> e
        | None, IfExpr (_, Operation (_, Eq, [Var (_, x); _]), _, _) when List.exists (fun (t, y) -> y = x) ps -> Var (l, x)
        | _, _ -> raise (ParseException (l, "If the body of a fixpoint function is not of the form '{ switch (_) {_} }' or '{ return x == _ ? _ : _; }', a decreases clause must be specified"))
      in
      let gmeasure = g ^ "__measure" in
      let call g args = CallExpr (l, g, [], [], List.map (fun e -> LitPat e) args, Static) in
      [
        Func (l, Fixpoint, tparams, Some rt, gdef, (PureFuncTypeExpr (l, List.map fst ps @ [rt]), g) :: ps, false, None, None, false, body, false, []);
        Inductive (l, iargs, tparams, [Ctor (l, iargs, List.map (fun (t, x) -> (x, t)) ps)]);
        Func (l, Fixpoint, tparams, Some rt, g_uncurry, (PureFuncTypeExpr (l, [iargsType; rt]), g) :: ps, false, None, None, false,
          Some ([ReturnStmt (l, Some (call g [call iargs (List.map (fun (t, x) -> Var (l, x)) ps)]))], l), false, []);
        Func (l, Fixpoint, tparams, Some rt, gdef_curried, [PureFuncTypeExpr (l, [iargsType; rt]), g; iargsType, "__args"], false, None, None, false,
          Some ([SwitchStmt (l, Var (l, "__args"), [SwitchStmtClause (l, call iargs (List.map (fun (t, x) -> Var (l, x)) ps),
            [ReturnStmt (l, Some (call gdef ([ExprCallExpr (l, Var (l, g_uncurry), [Var (l, g)])] @ List.map (fun (t, x) -> Var (l, x)) ps)))])])], l), false, []);
        Func (l, Fixpoint, tparams, Some (ManifestTypeExpr (l, intType)), gmeasure, [iargsType, "__args"], false, None, None, false,
          Some ([SwitchStmt (l, Var (l, "__args"), [SwitchStmtClause (l, call iargs (List.map (fun (t, x) -> Var (l, x)) ps),
            [ReturnStmt (l, Some measure)])])], l), false, []);
        Func (l, Fixpoint, tparams, Some rt, g, ps, false, None, None, false, Some ([ReturnStmt (l, Some (call "fix" [Var (l, gdef_curried); Var (l, gmeasure); call iargs (List.map (fun (t, x) -> Var (l, x)) ps)]))], l), false, []);
        Func (l, Lemma (kwd = "fixpoint_auto", None), tparams, None, g ^ "_def", ps, false, None,
          Some (Operation (l, Le, [IntLit (l, zero_big_int, true, false, NoLSuffix); measure]), Operation (l, Eq, [call g (List.map (fun (t, x) -> Var (l, x)) ps); bodyExpr])),
          false,
          Some ([
            IfStmt (l, Operation (l, Neq, [call g (List.map (fun (t, x) -> Var (l, x)) ps); bodyExpr]), [
              ExprStmt (call "fix_unfold" [Var (l, gdef_curried); Var (l, gmeasure); call iargs (List.map (fun (t, x) -> Var (l, x)) ps)]);
              Open (l, None, "exists", [], [], [CtorPat (l, "pair", [CtorPat (l, "pair", [VarPat (l, "f1__"); VarPat (l, "f2__")]); CtorPat (l, iargs, List.map (fun (t, x) -> VarPat (l, x ^ "0")) ps)])], None);
              Assert (l, (MatchAsn (l, call "pair" [ExprCallExpr (l, Var (l, g_uncurry), [Var (l, "f1_")]); ExprCallExpr (l, Var (l, g_uncurry), [Var (l, "f2_")])],
                CtorPat (l, "pair", [VarPat (l, g ^ "__1"); VarPat (l, g ^ "__2")]))));
              Assert (l, Operation (l, Eq, [
                call gdef ([Var (l, g ^ "__1")] @ List.map (fun (t, x) -> Var (l, x ^ "0")) ps);
                call gdef ([Var (l, g ^ "__2")] @ List.map (fun (t, x) -> Var (l, x ^ "0")) ps)]))
            ], [])
          ], l), false, [])
      ]
    | _ ->
      if kwd = "fixpoint_auto" then raise (ParseException (l, "Keyword 'fixpoint_auto' does not make sense here because this type of fixpoint definition is always unfolded automatically"));
      [Func (l, Fixpoint, tparams, rt, g, ps, false, None, None, false, body, false, [])]
    end
and
  parse_action_decls = function%parser
| [ parse_action_decl as ad; 
    parse_action_decls as ads 
  ] -> ad::ads
| [ ] -> []
and
  parse_action_decl = function%parser
| [ (l, Kwd "action"); 
    [%l
    permbased = opt (function%parser 
    | [ (_, Kwd "permbased") ] -> 0
    )
    ]; 
    (_, Ident an); 
    parse_paramlist as ps; 
    (_, Kwd ";");
    (_, Kwd "requires"); 
    parse_expr as pre; 
    (_, Kwd ";");
    (_, Kwd "ensures"); 
    parse_expr as post; 
    (_, Kwd ";") 
  ] -> ActionDecl (l, an, (match permbased with None -> false | Some _ -> true), ps, pre, post)
and
  parse_handle_pred_decls = function%parser
| [ parse_handle_pred_decl as hpd; 
    parse_handle_pred_decls as hpds 
  ] -> hpd::hpds
| [ ] -> []
and
  parse_handle_pred_decl = function%parser
  [ (l, Kwd "handle_predicate"); 
  (_, Ident hpn); 
  parse_paramlist as ps;
  [%l 
  extends = opt (function%parser 
  | [ (l, Kwd "extends"); 
      (_, Ident ehn) 
    ] -> ehn
  )
  ];
  (_, Kwd "{"); 
  (_, Kwd "invariant"); 
  parse_asn as inv; 
  (_, Kwd ";"); 
  parse_preserved_by_clauses as pbcs; 
  (_, Kwd "}") 
  ] -> HandlePredDecl (l, hpn, ps, extends, inv, pbcs)
and
  parse_preserved_by_clauses = function%parser
| [ parse_preserved_by_clause as pbc; 
    parse_preserved_by_clauses as pbcs 
  ] -> pbc::pbcs
| [ ] -> []
and
  parse_preserved_by_clause = function%parser
| [ (l, Kwd "preserved_by"); 
    (_, Ident an); 
    (_, Kwd "("); 
    [%l
    xs = rep_comma (function%parser 
    | [ (_, Ident x) ] -> x
    )
    ]; 
    (_, Kwd ")");
    parse_block as ss 
  ] -> PreservedByClause (l, an, xs, ss)
and
  parse_type_params_free = function%parser 
| [ (_, Kwd "<"); 
    [%l 
    xs = rep_comma (function%parser 
    | [ (_, Ident x) ] -> x
    )
    ]; 
    (_, Kwd ">") 
  ] -> xs
and
  parse_type_params_general = function%parser
| [ parse_type_params_free as xs ] -> xs
| [ [%l
    xs = peek_in_ghost_range (function%parser 
    | [ parse_type_params_free as xs;
        (_, Kwd "@*/")
      ] -> xs
    )
    ]
  ] -> xs
| [ ] -> []
and 
  type_params_parse = function%parser
| [ [%l xs = opt parse_type_params_general] ] ->
    match xs with
    | Some(params) -> params
    | None -> []
and
  parse_func_rest k t = function%parser
| [ (l, Ident g);
    parse_type_params_general as tparams;
    [%l
    decl = function%parser
    | [ (_, Kwd "(");
        [%l () = (fun _ -> push_typedef_scope ())];
        [%l ps = rep_comma parse_param];
        [%l ps = (fun _ -> List.filter filter_void_params ps)];
        (_, Kwd ")");
        [%l
        f = function%parser
        | [ (_, Kwd ";"); 
            [%l (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses] 
          ] -> Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, terminates, None, false, [])
        | [ [%l (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses]; 
            (_, Kwd "{"); 
            parse_stmts as ss; 
            (closeBraceLoc, Kwd "}") 
          ] -> Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, terminates, Some (ss, closeBraceLoc), false, [])
        ]
      ] -> pop_typedef_scope (); f
    | [ [%l () = (fun s -> if k = Regular && tparams = [] && t <> None then () else raise Stream.Failure)];
        [%l t = parse_array_braces (get t)];
        [%l
        init = opt (function%parser 
        | [ (_, Kwd "="); 
            [%l e = parse_declaration_rhs t] 
          ] -> e
        )
        ];
        (_, Kwd ";")
      ] ->
      let t =
        match t, init with
          ArrayTypeExpr (l, elemTp), Some (InitializerList (_, es)) ->
          StaticArrayTypeExpr (l, elemTp, List.length es)
        | _ -> t
      in
      Global (l, t, g, init)
    ]
  ] -> decl
and
  parse_ctors_suffix = function%parser
| [ (_, Kwd "|"); 
    parse_ctors as cs 
  ] -> cs
| [ ] -> []
and
  parse_ctors = function%parser
| [ (l, Ident cn);
    [%l
    ts = begin function%parser
    | [ (_, Kwd "(");
        [%l ts = rep_comma parse_paramtype_and_name];
        (_, Kwd ")")
      ] -> ts
    | [ ] -> []
    end
    ];
    parse_ctors_suffix as cs
  ] -> Ctor (l, cn, ts)::cs
and
  parse_paramtype_and_name = function%parser
| [ parse_type as t;
    [%l 
    paramname_opt = opt (function%parser
    | [ (_, Ident paramname) ] -> paramname
    )
    ]
  ] ->
    let paramname = match paramname_opt with None -> "" | Some(x) -> x in
    (paramname, t)
and
  parse_paramtype = function%parser [ parse_type as t; [%l _d = opt (function%parser [ (_, Ident _) ] -> ())] ] -> t
and
  parse_fields = function%parser
| [ (_, Kwd "{"); 
    parse_fields_rest as fs 
  ] -> fs
and
  parse_fields_rest = function%parser
| [ (_, Kwd "}") ] -> []
| [ parse_field as f; 
    parse_fields_rest as fs 
  ] -> f::fs
and
  parse_field = function%parser
| [ (_, Kwd "/*@"); 
    [%l f = parse_field_core Ghost]; 
    (_, Kwd "@*/") 
  ] -> f
| [ [%l f = parse_field_core Real] ] -> f
and
  parse_field_core gh = function%parser
| [ parse_type as te0; 
    (l, Ident f);
    [%l
    te = function%parser
    | [ (_, Kwd ";") ] -> te0
    | [ (_, Kwd "["); 
        (ls, Int (size, _, _, _, _)); 
        (_, Kwd "]"); 
        (_, Kwd ";") 
      ] ->
        if int_of_big_int size <= 0 then
          raise (ParseException (ls, "Array must have size > 0."));
        StaticArrayTypeExpr (l, te0, int_of_big_int size)
    ]
  ] -> Field (l, gh, te, f, Instance, Public, false, None)
and
  parse_struct_attrs = function%parser (* GCC-style attributes are always in double parentheses, see https://gcc.gnu.org/onlinedocs/gcc/Variable-Attributes.html *)
  [ (_, Kwd "("); 
    (_, Kwd "("); 
    [%l attrs = rep_comma parse_struct_attr]; 
    (_, Kwd ")"); 
    (_, Kwd ")"); 
  ] -> attrs
and
  parse_struct_attr = function%parser
| [ (_, Ident "packed") ] -> Packed
and
  parse_return_type = function%parser
| [ parse_type as t ] -> match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t
and
  parse_type = function%parser
| [ parse_primary_type as t0; 
    [%l t = parse_type_suffix t0] 
  ] -> t
and
  parse_int_opt = function%parser
| [ (_, Kwd "int") ] -> ()
| [ ] -> ()
and
  parse_integer_type_keyword = function%parser
| [ (l, Kwd "int") ] -> (l, IntRank)
| [ (l, Kwd "__int8") ] -> (l, FixedWidthRank 0)
| [ (l, Kwd "__int16") ] -> (l, FixedWidthRank 1)
| [ (l, Kwd "__int32") ] -> (l, FixedWidthRank 2)
| [ (l, Kwd "__int64") ] -> (l, FixedWidthRank 3)
| [ (l, Kwd "__int128") ] -> (l, FixedWidthRank 4)
and
  parse_integer_size_specifier = function%parser
| [ (_, Kwd "short") ] -> ShortRank
| [ (_, Kwd "long");
    [%l
    n = begin function%parser
    | [ (_, Kwd "long") ] -> LongLongRank
    | [ ] -> LongRank
    end
    ] 
  ] -> n
| [ ] -> IntRank
and
  parse_integer_type_rest = function%parser
| [ (_, Kwd "char") ] -> CharRank
| [ [%l (_d, k) = parse_integer_type_keyword] ] -> k
| [ parse_integer_size_specifier as n; 
    [%l _d = opt (function%parser [ (_, Kwd "int") ] -> ())] 
  ] -> n
and
  parse_primary_type = function%parser
| [ (l, Kwd "volatile"); 
    parse_primary_type as t0 
  ] -> t0
| [ (l, Kwd "const"); 
    parse_primary_type as t0 
  ] -> t0
| [ (l, Kwd "register"); 
    parse_primary_type as t0 
  ] -> t0
| [ (l, Kwd "struct"); 
    [%l
    sn = opt (function%parser 
    | [ (_, Ident s) ] -> s
    )
    ]; 
    [%l fs = opt parse_fields]; 
    [%l
    attrs = begin function%parser
    | [ (_, Kwd "__attribute__"); 
        parse_struct_attrs as res 
      ] -> res
    | [ ] -> [] 
    end 
    ]
  ] ->
  if sn = None && fs = None then raise (ParseException (l, "Struct name or body expected"));
  StructTypeExpr (l, sn, fs, attrs)
| [ (l, Kwd "union"); 
    [%l un = opt (function%parser [ (_, Ident u) ] -> u)]; 
    [%l fs = opt parse_fields]
  ] ->
  if un = None && fs = None then raise (ParseException (l, "Union name or body expected"));
  UnionTypeExpr (l, un, fs)
| [ (l, Kwd "enum"); 
    [%l en = opt (function%parser [ (_, Ident en) ] -> en)]; 
    [%l body = opt parse_enum_body] 
  ] ->
  if en = None && body = None then raise (ParseException (l, "Enum name or body expected"));
  EnumTypeExpr (l, en, body)
| [ [%l (l, k) = parse_integer_type_keyword] ] -> ManifestTypeExpr (l, Int (Signed, k))
| [ (l, Kwd "float") ] -> ManifestTypeExpr (l, Float)
| [ (l, Kwd "double") ] -> ManifestTypeExpr (l, Double)
| [ (l, Kwd "short") ] -> ManifestTypeExpr(l, Int (Signed, ShortRank))
| [ (l, Kwd "long");
    [%l
    t = begin function%parser
    | [ (_, Kwd "int") ] -> ManifestTypeExpr (l, longType);
    | [ (_, Kwd "double") ] -> ManifestTypeExpr (l, LongDouble);
    | [ (_, Kwd "long"); 
        [%l 
        _d = opt (function%parser 
        | [ (_, Kwd "int") ] -> ()
        ) 
        ]
      ] -> ManifestTypeExpr (l, Int (Signed, LongLongRank))
    | [ ] -> ManifestTypeExpr (l, longType)
    end
    ]
  ] -> t
| [ (l, Kwd "signed"); 
    parse_integer_type_rest as n 
  ] -> ManifestTypeExpr (l, Int (Signed, n))
| [ (l, Kwd "__signed__"); 
    parse_integer_type_rest as n
  ] -> ManifestTypeExpr (l, Int (Signed, n))
| [ (l, Kwd "unsigned"); 
    parse_integer_type_rest as n 
  ] -> ManifestTypeExpr (l, Int (Unsigned, n))
| [ (l, Kwd "uintptr_t") ] -> ManifestTypeExpr (l, Int (Unsigned, PtrRank))
| [ (l, Kwd "intptr_t") ] -> ManifestTypeExpr (l, Int (Signed, PtrRank))
| [ (l, Kwd "real") ] -> ManifestTypeExpr (l, RealType)
| [ (l, Kwd "bool") ] -> ManifestTypeExpr (l, Bool)
| [ (l, Kwd "boolean") ] -> ManifestTypeExpr (l, Bool)
| [ (l, Kwd "void") ] -> ManifestTypeExpr (l, Void)
| [ (l, Kwd "char") ] -> ManifestTypeExpr (l, match language with CLang -> Int (Signed, CharRank) | Java -> java_char_type)
| [ (l, Kwd "byte") ] -> ManifestTypeExpr (l, java_byte_type)
| [ (l, Kwd "predicate");
    (_, Kwd "(");
    [%l ts = rep_comma parse_paramtype];
    [%l ts' = opt (function%parser [ (_, Kwd ";"); [%l ts' = rep_comma parse_paramtype] ] -> ts')];
    (_, Kwd ")")
  ] -> begin match ts' with None -> PredTypeExpr (l, ts, None) | Some ts' -> PredTypeExpr (l, ts @ ts', Some (List.length ts)) end
| [ (l, Kwd "fixpoint"); 
    (_, Kwd "("); 
    [%l ts = rep_comma parse_paramtype]; 
    (_, Kwd ")") 
  ] -> PureFuncTypeExpr (l, ts)
| [ (l, Kwd "box") ] -> ManifestTypeExpr (l, BoxIdType)
| [ (l, Kwd "handle") ] -> ManifestTypeExpr (l, HandleIdType)
| [ (l, Kwd "any") ] -> ManifestTypeExpr (l, AnyType)
| [ (l, Ident n); 
    [%l
    rest = rep (function%parser 
    | [ (l, Kwd "."); 
        (l, Ident n) 
      ] -> n
    )
    ]; 
    [%l (targs, diamond) = parse_type_args_with_diamond l] 
  ] -> 
  if diamond then ConstructedTypeExpr(l,n, []) else
  if targs <> [] then 
    match rest with
    | [] -> ConstructedTypeExpr (l, n, targs) 
    | _ -> raise (ParseException (l, "Package name not supported for generic types."))
  else
    match rest with
      [] -> IdentTypeExpr(l, None, n)
    | _ -> 
    let pac = (String.concat "." (n :: (take ((List.length rest) -1) rest))) in
    IdentTypeExpr(l, Some (pac), List.nth rest ((List.length rest) - 1))
and
  parse_type_suffix t0 = function%parser
| [ (l, Kwd "*"); 
    [%l t = parse_type_suffix (PtrTypeExpr (l, t0))] 
  ] -> t
| [ (l, Kwd "volatile"); 
    [%l t = parse_type_suffix t0] 
  ] -> t
| [ (l, Kwd "const"); 
    [%l t = parse_type_suffix t0] 
  ] -> t
| [ (l, Kwd "["); 
    (_, Kwd "]"); 
    [%l t = parse_type_suffix (ArrayTypeExpr (l,t0))] 
  ] when language = Java -> t
| [ ] -> t0
and
(* parse function parameters: *)
  parse_paramlist = function%parser
| [ (_, Kwd "("); 
    [%l ps = rep_comma parse_param]; 
    (_, Kwd ")") 
  ] -> List.filter filter_void_params ps
and
  filter_void_params ps = match ps with
    (ManifestTypeExpr (_, Void), "") -> false
  | _ -> true
and
  parse_param = function%parser
| [ parse_type as t; 
    parse_declarator0 as f 
  ] ->
    let (t, pn) = f t in
    begin match t with
      ManifestTypeExpr (_, Void) -> 
      begin match pn with
        None -> (t, "")
      | Some((l, pname)) -> raise (ParseException (l, "A parameter cannot be of type void."))
      end
    | _ -> 
      begin match pn with
        None -> (t, get_unnamed_param_name ())
      | Some((l, pname)) -> 
        register_varname pname;
        (t, pname)
      end
    end
| [ (l, Kwd "...") ] -> (ConstructedTypeExpr (l, "list", [IdentTypeExpr (l, None, "vararg")]), "varargs")
and
  parse_functypeclause_args = function%parser
| [ (_, Kwd "("); 
    [%l 
    args = rep_comma (function%parser 
    | [ (l, Ident x) ] -> (l, x)
    )
    ]; 
    (_, Kwd ")") 
  ] -> args
| [ ] -> []
and
  parse_pure_spec_clause = function%parser
| [ (_, Kwd "nonghost_callers_only") ] -> NonghostCallersOnlyClause
| [ (l, Kwd "terminates"); 
    (_, Kwd ";") 
  ] -> TerminatesClause l
| [ (_, Kwd ":"); 
    (li, Ident ft); 
    [%l targs = parse_type_args li]; 
    parse_functypeclause_args as ftargs 
  ] -> FuncTypeClause (ft, targs, ftargs)
| [ (_, Kwd "requires"); 
    parse_asn as p; 
    (_, Kwd ";") 
  ] -> RequiresClause p
| [ (_, Kwd "ensures"); 
    parse_asn as p; 
    (_, Kwd ";") 
  ] -> EnsuresClause p
and
  parse_spec_clause = function%parser
| [ [%l
    c = peek_in_ghost_range (function%parser 
        | [ parse_pure_spec_clause as c; 
            (_, Kwd "@*/") 
          ] -> c
        )
    ] 
  ] -> c
| [ parse_pure_spec_clause as c ] -> c
and
  parse_spec_clauses = fun token_stream ->
    let in_count = ref 0 in
    let out_count = ref 0 in
    let clause_stream = Stream.from (fun _ -> try let clause = Some (parse_spec_clause token_stream) in in_count := !in_count + 1; clause with Stream.Failure -> None) in
    let nonghost_callers_only = (function%parser [ NonghostCallersOnlyClause ] -> out_count := !out_count + 1; true | [ ] -> false) clause_stream in
    let ft = (function%parser [ FuncTypeClause (ft, fttargs, ftargs) ] -> out_count := !out_count + 1; Some (ft, fttargs, ftargs) | [ ] -> None) clause_stream in
    let pre_post = (function%parser [ RequiresClause pre; EnsuresClause post; ] -> out_count := !out_count + 2; Some (pre, post) | [ ] -> None) clause_stream in
    let terminates = (function%parser [ (TerminatesClause l) ] -> out_count := !out_count + 1; true | [ ] -> false) clause_stream in
    if !in_count > !out_count then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: nonghost_callers_only clause (optional), function type clause (optional), contract (optional), terminates clause (optional).");
    (nonghost_callers_only, ft, pre_post, terminates)
and
  parse_spec = function%parser
| [ [%l (nonghost_callers_only, ft, pre_post, terminates) = parse_spec_clauses] ] ->
    match (nonghost_callers_only, ft, pre_post) with
      (false, None, None) -> raise Stream.Failure
    | (false, None, (Some (pre, post))) -> (pre, post, terminates)
    | _ -> raise (Stream.Error "Incorrect kind, number, or order of specification clauses. Expected: requires clause, ensures clause, terminates clause (optional).")
and
  parse_block = function%parser
| [ (l, Kwd "{"); 
    parse_stmts as ss; 
    (_, Kwd "}") 
  ] -> ss
and
  parse_block_stmt = function%parser
| [ (l, Kwd "{");
    [%l
    (l, ds, ss, locals_to_free) = (function%parser
    | [ (Lexed (sp1, _), Kwd "/*@");
        [%l
        b = function%parser
        | [ parse_pure_decl as d; 
            parse_pure_decls as ds; 
            (_, Kwd "@*/"); 
            parse_stmts as ss 
          ] -> (l, d @ ds, ss, ref [])
        | [ parse_stmt0 as s; 
            (Lexed (_, sp2), Kwd "@*/"); 
            parse_stmts as ss 
          ] -> (l, [], PureStmt (Lexed (sp1, sp2), s)::ss, ref [])
        ]
       ] -> b
    | [ parse_pure_decls as ds; 
        parse_stmts as ss 
      ] -> (l, ds, ss, ref [])
    )
    ];
    (closeBraceLoc, Kwd "}")
  ] -> BlockStmt(l, ds, ss, closeBraceLoc, locals_to_free)
and
  parse_stmts = function%parser
| [ parse_stmt as s; 
    parse_stmts as ss 
  ] -> s::ss
| [ ] -> []
and
  parse_stmt = function%parser [ parse_stmt0 as s ] -> !stats#stmtParsed; s
and
  parse_coef = function%parser
| [ (l, Kwd "["); 
    parse_pattern as pat; 
    (_, Kwd "]") 
  ] -> pat
and parse_producing_handle_predicate = function%parser
| [ (lph, Ident post_hpn); 
    parse_arglist as post_hp_args; 
  ] -> (lph, post_hpn, post_hp_args)
and
  parse_producing_handle_predicate_list = function%parser
| [ (l, Kwd "if"); 
    (_, Kwd "("); 
    parse_expr as condition; 
    (_, Kwd ")"); 
    [%l (lph, post_hpn, post_hp_args) = parse_producing_handle_predicate]; 
    (_, Kwd "else"); 
    parse_producing_handle_predicate_list as rest 
  ] -> ConditionalProducingHandlePredicate(lph, condition, post_hpn, post_hp_args, rest); 
| [ [%l (lph, post_hpn, post_hp_args) = parse_producing_handle_predicate] ] -> BasicProducingHandlePredicate(lph, post_hpn, post_hp_args)
and
  parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause = function%parser
| [ (li, Ident ftn);
    [%l targs = parse_type_args li];
    parse_arglist as args;
    (_, Kwd "("); 
    [%l params = rep_comma (function%parser [ (l, Ident x) ] -> (l, x))]; 
    (_, Kwd ")");
    (openBraceLoc, Kwd "{"); 
    parse_stmts as ss; 
    (closeBraceLoc, Kwd "}") 
  ] -> (ftn, targs, args, params, openBraceLoc, ss, closeBraceLoc)
and
  parse_stmt0 = function%parser
| [ (Lexed (sp1, _), Kwd "/*@"); 
    parse_stmt0 as s; (Lexed (_, sp2), Kwd "@*/") 
  ] -> PureStmt (Lexed (sp1, sp2), s)
| [ (Lexed (sp1, _), Kwd "@*/"); 
    parse_stmt as s; 
    (Lexed (_, sp2), Kwd "/*@") 
  ] -> NonpureStmt (Lexed (sp1, sp2), false, s)
| [ (l, Kwd "if"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")"); 
    parse_stmt as s1;
    [%l
    s = function%parser
    | [ (_, Kwd "else"); 
        parse_stmt as s2 
      ] -> IfStmt (l, e, [s1], [s2])
    | [ ] -> IfStmt (l, e, [s1], [])
    ]
  ] -> s
| [ (l, Kwd "switch"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")"); 
    (_, Kwd "{"); 
    parse_switch_stmt_clauses as sscs; 
    (_, Kwd "}") 
  ] -> SwitchStmt (l, e, sscs)
| [ (l, Kwd "assert"); 
    parse_asn as p; 
    (_, Kwd ";") 
  ] -> Assert (l, p)
| [ (l, Kwd "leak"); 
    parse_asn as p; 
    (_, Kwd ";") 
  ] -> Leak (l, p)
| [ (l, Kwd "open"); 
    [%l coef = opt parse_coef]; 
    parse_expr as e; 
    (_, Kwd ";") 
  ] ->
  (match e with
     CallExpr (_, g, targs, es1, es2, Static) ->
       !stats#openParsed;
       Open (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       !stats#openParsed;
       Open (l, Some target, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [ (l, Kwd "close"); 
    [%l coef = opt parse_coef]; 
    parse_expr as e; 
    (_, Kwd ";") 
  ] ->
  (match e with
     CallExpr (_, g, targs, es1, es2, Static) ->
       !stats#closeParsed;
       Close (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       !stats#closeParsed;
       Close (l, Some target, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of close statement must be call expression.")))
| [ (l, Kwd "split_fraction"); 
    (li, Ident p); 
    [%l targs = parse_type_args li]; 
    parse_patlist as pats;
    [%l
    coefopt = (function%parser 
    | [ (_, Kwd "by"); 
        parse_expr as e 
      ] -> Some e 
    | [ ] -> None
    )
    ];
    (_, Kwd ";") 
  ] -> SplitFractionStmt (l, p, targs, pats, coefopt)
| [ (l, Kwd "merge_fractions"); 
    parse_asn as a; 
    (_, Kwd ";") 
  ]
  -> MergeFractionsStmt (l, a)
| [ (l, Kwd "dispose_box"); 
    (_, Ident bcn); 
    parse_patlist as pats;
    [%l
    handleClauses = rep (function%parser 
    | [ (l, Kwd "and_handle"); 
        (_, Ident hpn); 
        parse_patlist as pats 
      ] -> (l, hpn, pats)
    )
    ];
    (_, Kwd ";") 
  ] -> DisposeBoxStmt (l, bcn, pats, handleClauses)
| [ (l, Kwd "create_box"); 
    (_, Ident x); 
    (_, Kwd "="); 
    (_, Ident bcn); 
    parse_arglist as args;
    [%l lower_bounds = opt (function%parser [ (l, Kwd "above"); [%l es = rep_comma parse_expr] ] -> es)];
    [%l upper_bounds = opt (function%parser [ (l, Kwd "below"); [%l es = rep_comma parse_expr] ] -> es)];
    [%l
    handleClauses = rep (function%parser 
    | [ (l, Kwd "and_handle"); 
        (_, Ident x); 
        (_, Kwd "="); 
        (_, Ident hpn); 
        parse_arglist as args 
      ] -> (l, x, false, hpn, args)
    | [ (l, Kwd "and_fresh_handle"); 
        (_, Ident x); 
        (_, Kwd "="); 
        (_, Ident hpn); 
        parse_arglist as args 
      ] -> (l, x, true, hpn, args)
    )
    ];
    (_, Kwd ";")
  ] -> CreateBoxStmt (l, x, bcn, args, (match lower_bounds with None -> [] | Some lbs -> lbs), (match upper_bounds with None -> [] | Some ubs -> ubs), handleClauses)
| [ (l, Kwd "produce_lemma_function_pointer_chunk");
    [%l
    (e, ftclause) = begin function%parser
    | [ (_, Kwd "("); 
        parse_expr as e; 
        (_, Kwd ")");
        [%l
        ftclause = opt (function%parser 
        | [ (_, Kwd ":"); 
            parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause as ftclause 
          ] -> ftclause
        )
        ]
      ] -> (Some e, ftclause)
    | [ parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause as ftclause ] -> (None, Some ftclause)
    end
    ];
    [%l
    body = function%parser
    | [ (_, Kwd ";") ] -> None
    | [ parse_stmt as s ] -> Some s
    ]
  ] -> ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause, body)
| [ (l, Kwd "duplicate_lemma_function_pointer_chunk"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")"); 
    (_, Kwd ";")
  ] -> DuplicateLemmaFunctionPointerChunkStmt (l, e)
| [ (l, Kwd "produce_function_pointer_chunk"); 
    (li, Ident ftn);
    [%l targs = parse_type_args li];
    (_, Kwd "("); 
    parse_expr as fpe; 
    (_, Kwd ")");
    parse_arglist as args;
    (_, Kwd "("); 
    [%l
    params = rep_comma (function%parser 
    | [ (l, Ident x) ] -> (l, x)
    )
    ]; 
    (_, Kwd ")");
    (openBraceLoc, Kwd "{"); 
    parse_stmts as ss; 
    (closeBraceLoc, Kwd "}") 
  ] ->
  ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc)
| [ (l, Kwd "goto"); 
    (_, Ident lbl); 
    (_, Kwd ";") 
  ] -> GotoStmt (l, lbl)
| [ (l, Kwd "invariant"); 
    parse_asn as inv; 
    (_, Kwd ";") 
  ] -> InvariantStmt (l, inv)
| [ (l, Kwd "return"); 
    [%l
    eo = function%parser 
    | [ (_, Kwd ";") ] -> None 
    | [ parse_expr as e; 
        (_, Kwd ";") 
      ] -> Some e 
    ]
  ] -> ReturnStmt (l, eo)
| [ (l, Kwd "while"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")");
    [%l (inv, dec, body) = parse_loop_core l]
  ] -> WhileStmt (l, e, inv, dec, body, [])
| [ (l, Kwd "do"); 
    [%l (inv, dec, body) = parse_loop_core l]; 
    (lwhile, Kwd "while"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")"); 
    (_, Kwd ";") 
  ] ->
  (* "do S while (E);" is translated to "while (true) { S if (E) {} else break; }" *)
  WhileStmt (l, True l, inv, dec, body,  [IfStmt (lwhile, e, [], [Break lwhile])])
| [ (l, Kwd "for");
    (_, Kwd "(");
    [%l
    init_stmts = begin function%parser
    | [ parse_expr as e;
        [%l
        ss = function%parser
        | [ (l, Ident x); 
            [%l s = parse_decl_stmt_rest (type_expr_of_expr e) l x] 
          ] -> register_varname x; [s]
        | [ [%l es = comma_rep parse_expr]; 
            (_, Kwd ";") 
          ] -> List.map (fun e -> ExprStmt e) (e::es)
        ]
      ] -> ss
    | [ parse_type as te; 
        (l, Ident x); 
        [%l s = parse_decl_stmt_rest te l x] 
      ] -> register_varname x; [s]
    | [ (_, Kwd ";") ] -> []
    end
    ];
    [%l cond = opt parse_expr];
    (_, Kwd ";");
    [%l update_exprs = rep_comma parse_expr];
    (_, Kwd ")");
    [%l (inv, dec, b) = parse_loop_core l]
  ] ->
  let cond = match cond with None -> True l | Some e -> e in
  BlockStmt (l, [], init_stmts @ [WhileStmt (l, cond, inv, dec, b, List.map (fun e -> ExprStmt e) update_exprs)], l, ref [])
| [ (l, Kwd "throw");
    parse_expr as e; 
    (_, Kwd ";") 
  ] -> Throw (l, e)
| [ (l, Kwd "break"); 
    (_, Kwd ";") 
  ] -> Break(l)
| [ (l, Kwd "try");
    parse_block as body;
    [%l
    catches = rep (function%parser 
    | [ (l, Kwd "catch"); 
        (_, Kwd "("); 
        parse_type as t; 
        (_, Ident x); 
        (_, Kwd ")"); 
        parse_block as body 
      ] -> (l, t, x, body)
    )
    ];
    [%l
    finally = opt (function%parser 
    | [ (l, Kwd "finally"); 
        parse_block as body 
      ] -> (l, body)
    )
    ]
  ] ->
  begin match (catches, finally) with
    ([], Some (lf, finally)) -> TryFinally (l, body, lf, finally)
  | (catches, None) -> TryCatch (l, body, catches)
  | (catches, Some (lf, finally)) -> TryFinally (l, [TryCatch (l, body, catches)], lf, finally)
  end
| [ parse_block_stmt as s ] -> s
| [ (lcb, Kwd "consuming_box_predicate"); 
    (_, Ident pre_bpn); 
    parse_patlist as pre_bp_args;
    [%l
    consumed_handle_predicates = rep (function%parser
    | [ (lch, Kwd "consuming_handle_predicate"); 
        (_, Ident pre_hpn); 
        parse_patlist as pre_hp_args; 
      ] -> ConsumingHandlePredicate(lch, pre_hpn, pre_hp_args)
    )
    ];
    (lpa, Kwd "perform_action"); 
    (_, Ident an); 
    parse_arglist as aargs;
    (_, Kwd "{"); 
    parse_stmts as ss; 
    (closeBraceLoc, Kwd "}");
    [%l
    post_bp_args = opt begin function%parser
    | [ (lpb, Kwd "producing_box_predicate"); 
        (_, Ident post_bpn); 
        parse_arglist as post_bp_args 
      ] ->
        if post_bpn <> pre_bpn then raise (ParseException (lpb, "The box predicate name cannot change."));
        (lpb, post_bp_args)
    end
    ];
    [%l
    produced_handles = rep (function%parser
    | [ (_, Kwd "producing_handle_predicate"); 
        parse_producing_handle_predicate_list as producing_hp_list 
      ] -> (false, producing_hp_list)
    | [ (_, Kwd "producing_fresh_handle_predicate"); 
        parse_producing_handle_predicate_list as producing_hp_list 
      ] -> (true, producing_hp_list)
    )
    ];
    (_, Kwd ";") 
  ] -> PerformActionStmt (lcb, ref false, pre_bpn, pre_bp_args, consumed_handle_predicates, lpa, an, aargs, ss, closeBraceLoc, post_bp_args, produced_handles)
| [ (l, Kwd ";") ] -> NoopStmt l
| [ (l, Kwd "super"); 
    [%l
    s = function%parser 
    | [ (_, Kwd "."); 
        (l2, Ident n); 
        (_, Kwd "("); 
        [%l es = rep_comma parse_expr]; 
        (_, Kwd ")") 
      ] -> ExprStmt(SuperMethodCall (l, n, es))
   | [ (_, Kwd "("); 
      [%l es = rep_comma parse_expr]; 
      (_, Kwd ")"); 
      (_, Kwd ";") 
      ] -> SuperConstructorCall (l, es)
    ]
  ] -> s
| [ parse_expr as e; 
    [%l
    s = function%parser
    | [ (_, Kwd ";") ] ->
      begin match e with
        AssignExpr (l, Operation (llhs, Mul, [Var (lt, t); e1]), rhs) -> 
        let rec iter te e1 =
          match e1 with
            Var (lx, x) -> register_varname x; DeclStmt (l, [l, te, x, Some(rhs), (ref false, ref None)])
          | Deref (ld, e2) -> iter (PtrTypeExpr (ld, te)) e2
          | _ -> ExprStmt e
        in
        iter (PtrTypeExpr (llhs, IdentTypeExpr (lt, None, t))) e1
      | Operation (l, Mul, [Var (lt, t); e1]) ->
        let rec iter te e1 =
          match e1 with
            Var (lx, x) -> register_varname x; DeclStmt (lx, [lx, te, x, None, (ref false, ref None)])
          | Deref (ld, e2) -> iter (PtrTypeExpr (ld, te)) e2
          | _ -> ExprStmt e
        in
        iter (PtrTypeExpr (l, IdentTypeExpr (lt, None, t))) e1
      | _ -> ExprStmt e
      end
    | [ (l, Kwd ":") ] -> (match e with Var (_, lbl) -> LabelStmt (l, lbl) | _ -> raise (ParseException (l, "Label must be identifier.")))
    | [ (lx, Ident x); 
        [%l s = parse_decl_stmt_rest (type_expr_of_expr e) lx x] 
      ] -> register_varname x; s
    ]
  ] -> s
(* parse variable declarations: *)
| [ parse_type as te; 
    (lx, Ident x); 
    [%l s2 = parse_decl_stmt_rest te lx x] 
  ] ->
  register_varname x;
  ( try match te with
     ManifestTypeExpr (l, Void) ->
      raise (ParseException (l, "A variable cannot be of type void."))
    with
     Match_failure _ -> s2 )
and
  parse_loop_core l = function%parser 
| [ [%l (inv, dec) = parse_loop_core0 l];
    parse_stmt as body
  ] -> (inv, dec, [body])
and
  parse_loop_core0 l = function%parser 
| [ [%l 
    inv = opt begin function%parser
    | [ (_, Kwd "/*@");
      [%l
      inv = begin function%parser
      | [ (_, Kwd "invariant"); 
          parse_asn as p; 
          (_, Kwd ";"); 
          (_, Kwd "@*/") 
        ] -> LoopInv p
      | [ (_, Kwd "requires"); 
          parse_asn as pre; 
          (_, Kwd ";"); 
          (_, Kwd "@*/");
          (_, Kwd "/*@"); 
          (_, Kwd "ensures"); 
          parse_asn as post; 
          (_, Kwd ";"); 
          (_, Kwd "@*/") 
        ] -> LoopSpec (pre, post)
      end
      ]
      ] -> inv
    | [ (_, Kwd "invariant"); 
        parse_asn as p; 
        (_, Kwd ";"); 
      ] -> LoopInv p
    end
    ];
    [%l
    dec = opt (function%parser 
    | [ (_, Kwd "/*@"); 
        (_, Kwd "decreases"); 
        parse_expr as decr; 
        (_, Kwd ";"); 
        (_, Kwd "@*/") 
      ] -> decr 
    | [ (_, Kwd "decreases"); 
        parse_expr as decr; 
        (_, Kwd ";"); 
      ] -> decr 
    )
    ];(* only allows decreases if invariant provided *)
  ] -> (inv, dec)
and
  packagename_of_read l e =
  match e with
  | Var(_, x) when x <> "this" -> x
  | Read(_, e, f) -> (packagename_of_read l e) ^ "." ^ f
  | e -> raise (ParseException (l, "Type expected."))
and
  type_expr_of_expr e =
  match e with
    Var (l, x) -> IdentTypeExpr (l, None, x)
  | CallExpr (l, x, targs, [], [], Static) -> ConstructedTypeExpr (l, x, targs)
  | ArrayTypeExpr' (l, e) -> ArrayTypeExpr (l, type_expr_of_expr e)
  | Read(l, e, name) -> IdentTypeExpr(l, Some(packagename_of_read l e), name)
  | e -> raise (ParseException (expr_loc e, "Type expected."))
and parse_array_braces te = function%parser
| [ (l, Kwd "[");
    [%l
    te = begin function%parser
    | [ (lsize, Lexer.Int (size, _, _, _, _)); 
        (_, Kwd "]"); 
        [%l te = parse_array_braces te] 
      ] ->
        if sign_big_int size <= 0 then raise (ParseException (lsize, "Array must have size > 0."));
        StaticArrayTypeExpr (l, te, int_of_big_int size)
    | [ (_, Kwd "]") ] ->
      ArrayTypeExpr (l, te)
    end
    ]
  ] -> te
| [ ] -> te
and parse_create_handle_keyword = function%parser 
| [ (l, Kwd "create_handle") ] -> (l, false)
| [ (l, Kwd "create_fresh_handle") ] -> (l, true)
and
  get_ultimate_pointee_type = function
    PtrTypeExpr (l, te) -> get_ultimate_pointee_type te
  | te -> te
and
  parse_decl_stmt_rest te lx x = function%parser
| [ (l, Kwd "=");
    [%l
    s = function%parser
    | [ [%l (l, fresh) = parse_create_handle_keyword]; 
        (_, Ident hpn); 
        (_, Kwd "("); 
        parse_expr as e; 
        (_, Kwd ")"); 
        (_, Kwd ";") 
      ] ->
        begin
          match te with ManifestTypeExpr (_, HandleIdType) -> () | _ -> raise (ParseException (l, "Target variable of handle creation statement must have type 'handle'."))
        end;
        CreateHandleStmt (l, x, fresh, hpn, e)
    | [ [%l rhs = parse_declaration_rhs te]; 
        [%l ds = comma_rep (parse_declarator (get_ultimate_pointee_type te))]; 
        (_, Kwd ";") 
      ] -> DeclStmt (l, (l, te, x, Some(rhs), (ref false, ref None))::ds)
    ]
  ] -> s
| [ [%l tx = parse_array_braces te];
    [%l
    init = opt (function%parser 
    | [ (_, Kwd "="); 
        [%l e = parse_declaration_rhs tx] 
      ] -> e
    )
    ];
    [%l ds = comma_rep (parse_declarator te)];
    (_, Kwd ";")
  ] ->
    let tx =
      match tx, init with
        ArrayTypeExpr (l, elemTp), Some (InitializerList (_, es)) when language = CLang ->
        StaticArrayTypeExpr (l, elemTp, List.length es)
      | _ -> tx
    in
    DeclStmt(type_expr_loc te, (lx, tx, x, init, (ref false, ref None))::ds)
and
  parse_switch_stmt_clauses = function%parser
| [ parse_switch_stmt_clause as c; 
    parse_switch_stmt_clauses as cs 
  ] -> c::cs
| [ ] -> []
and
  parse_switch_stmt_clause = function%parser
| [ (l, Kwd "case");
    [%l typedefs_enabled = (fun _ -> set_typedefs_enabled false)];
    parse_expr as e;
    [%l _d = (fun _ -> set_typedefs_enabled typedefs_enabled)];
    (_, Kwd ":");
    [%l _d = (fun _ -> register_pattern_varnames e)];
    parse_stmts as ss
  ] -> SwitchStmtClause (l, e, ss)
| [ (l, Kwd "default"); 
    (_, Kwd ":"); 
    parse_stmts as ss; 
  ] -> SwitchStmtDefaultClause(l, ss)
and
  register_pattern_varnames = function
    CallExpr (_, _, _, _, args, _) -> List.iter (function LitPat e -> register_pattern_varnames e | _ -> ()) args
  | Var (_, x) -> register_varname x
  | _ -> ()
and
  parse_more_pats = function%parser
  [ (_, Kwd ")") ] -> []
| [ (_, Kwd ","); 
    (lx, Ident x); 
    parse_more_pats as xs 
  ] -> register_varname x; x::xs
and
  parse_asn stream = parse_expr stream
and
  parse_asn0 = function%parser
| [ (l, Kwd "emp") ] -> EmpAsn l
| [ (l, Kwd "forall_"); 
    (_, Kwd "("); 
    parse_type as tp; 
    (_, Ident x); 
    (_, Kwd ";"); 
    parse_expr as e; 
    (_, Kwd ")") 
  ] -> ForallAsn(l, tp, x, e)
| [ (l, Kwd "["); 
    parse_pattern as coef; 
    (_, Kwd "]"); 
    parse_pointsto_expr as p 
  ] -> CoefAsn (l, coef, p)
| [ (l, Kwd "ensures"); 
    parse_asn as p 
  ] -> EnsuresAsn (l, p)
and
  parse_pointsto_rhs = function%parser
| [ (_, Kwd "_") ] -> DummyPat
| [ (_, Kwd "?"); 
    [%l
    p = function%parser 
    | [ (lx, Ident x) ] -> register_varname x; VarPat (lx, x) 
    | [ (_, Kwd "_") ] -> DummyVarPat 
    ]
  ] -> p
| [ (_, Kwd "^"); 
    parse_expr as e 
  ] -> LitPat (WidenedParameterArgument e)
| [ parse_cond_expr as e ] -> pat_of_expr e
and
  parse_pattern = function%parser
| [ (_, Kwd "_") ] -> DummyPat
| [ (_, Kwd "?"); (lx, Ident x) ] -> register_varname x; VarPat (lx, x)
| [ (_, Kwd "^"); parse_expr as e ] -> LitPat (WidenedParameterArgument e)
| [ parse_cond_expr as e ] -> pat_of_expr e
and
  parse_switch_asn_clauses = function%parser
| [ parse_switch_asn_clause as c; parse_switch_asn_clauses as cs ] -> c::cs
| [ ] -> []
and
  parse_switch_asn_clause = function%parser
| [ (l, Kwd "case"); 
    (_, Ident c); 
    [%l
    pats = (function%parser 
    | [ (_, Kwd "("); 
        (lx, Ident x); 
        [%l () = (fun _ -> register_varname x)]; 
        parse_more_pats as xs 
      ] -> x::xs 
    | [ ] -> []
    )
    ]; 
    (_, Kwd ":"); 
    (_, Kwd "return"); 
    parse_asn as p; 
    (_, Kwd ";") 
  ] -> SwitchAsnClause (l, c, pats, p)
and
  parse_expr stream = parse_assign_expr stream
and
  parse_assign_expr = function%parser
| [ parse_sep_expr as e0; [%l e = parse_assign_expr_rest e0] ] -> e
and
  parse_sep_expr = function%parser
| [ parse_pointsto_expr as e0; 
    [%l
    e = function%parser
    | [ (l, Kwd "&*&"); 
        parse_sep_expr as e1 
      ] -> Sep (l, e0, e1)
    | [ ] -> e0
    ]
  ] -> e
and
  parse_pointsto_expr = function%parser
| [ parse_cond_expr as e; 
    [%l
    e = function%parser
    | [ (l, Kwd "|->"); 
        parse_pointsto_rhs as rhs 
      ] -> 
        begin match e with
          ReadArray (_, _, SliceExpr (_, _, _)) -> PointsTo (l, e, rhs)
        | ReadArray (lr, e0, e1) when language = CLang -> PointsTo (l, Deref(lr, Operation(lr, Add, [e0; e1])), rhs) 
        | _ -> PointsTo (l, e, rhs)
        end
    | [ ] -> e
    ]
  ] -> e
and
  parse_cond_expr = function%parser
  [ parse_disj_expr as e0; 
    [%l
    e = function%parser
    | [ (l, Kwd "?"); 
        parse_expr as e1; 
        (_, Kwd ":"); 
        parse_sep_expr as e2 
      ] -> IfExpr (l, e0, e1, e2)
    | [ ] -> e0
    ]
  ] -> e
and
  parse_disj_expr = function%parser
| [ parse_conj_expr as e0; [%l e = parse_disj_expr_rest e0] ] -> e
and
  parse_conj_expr = function%parser
| [ parse_bitor_expr as e0; [%l e = parse_conj_expr_rest e0] ] -> e
and
  parse_bitor_expr = function%parser
| [ parse_bitxor_expr as e0; [%l e = parse_bitor_expr_rest e0] ] -> e
and
  parse_bitxor_expr = function%parser
| [ parse_bitand_expr as e0; [%l e = parse_bitxor_expr_rest e0] ] -> e
and
  parse_bitand_expr = function%parser
| [ parse_expr_rel as e0; [%l e = parse_bitand_expr_rest e0] ] -> e
and
  parse_expr_rel = function%parser
| [ parse_truncating_expr as e0; [%l e = parse_expr_rel_rest e0] ] -> e
and
  parse_truncating_expr = function%parser
| [ (l, Kwd "truncating"); parse_expr_suffix as e ] -> TruncatingExpr (l, e)
| [ [%l
    e = peek_in_ghost_range (function%parser 
    | [ (l, Kwd "truncating"); 
        (_, Kwd "@*/"); 
        parse_expr_suffix as e 
      ] -> TruncatingExpr (l, e)) 
    ]
  ] -> e
| [ parse_shift as e ] -> e
and
  parse_shift = function%parser
| [ parse_expr_arith as e0; [%l e = parse_shift_rest e0] ] -> e
and
  parse_expr_arith = function%parser
| [ parse_expr_mul as e0; [%l e = parse_expr_arith_rest e0] ] -> e
and
  parse_expr_mul = function%parser
| [ parse_expr_suffix as e0; [%l e = parse_expr_mul_rest e0] ] -> e
and
  parse_expr_suffix0 allowCast = function%parser
| [ [%l e0 = parse_expr_primary0 allowCast]; [%l e = parse_expr_suffix_rest e0] ] -> e
and
  parse_expr_suffix s = parse_expr_suffix0 true s
and
  parse_type_args l = function%parser
| [ [%l targs = parse_angle_brackets l (rep_comma parse_type)] ] -> targs
| [ ] -> []
and
  parse_type_args_with_diamond l0 = function%parser
| [ [%l
    (targs, diamond) = match language with
    | CLang -> 
      (function%parser 
      | [ [%l targs = parse_type_args l0] ] -> (targs, false)
      )
    | Java -> 
      (function%parser
      | [ (l1, Kwd "<"); 
          [%l
          (targs, diamond) = function%parser
          | [ (_, Kwd ">") ] -> ([], true)
          | [ [%l targs = rep_comma parse_type]; 
              (_, Kwd ">") 
            ] -> (targs, false) 
          ]
        ] -> (targs,diamond)
      | [ ] -> ([], false)
      )
    ]
  ] -> (targs, diamond)
and
  parse_new_array_expr_rest l elem_typ = function%parser
| [ (_, Kwd "[");
    [%l
    e = function%parser
    | [ parse_expr as length; 
        (_, Kwd "]"); 
      ] -> NewArray(l, elem_typ, length)
    | [ (_, Kwd "]"); 
        (_, Kwd "{"); 
        [%l es = rep_comma parse_expr]; 
        (_, Kwd "}") 
      ] -> NewArrayWithInitializer (l, elem_typ, es)
    ]
  ] -> e
and
  parse_expr_primary s = parse_expr_primary0 true s
and 
  parse_instance_call_rest l g targs target = function%parser
| [ parse_patlist as args0;
    [%l
    (args0, args) = begin function%parser
    | [ parse_patlist as args ] -> args0, args
    | [ ] -> [], args0
    end
    ]
  ] -> CallExpr (l, g, targs, args0, LitPat(target) :: args, Instance)
and
  parse_instance_call l target = 
    let parse_call_or_read lf f targs target read = function%parser
    | [ [%l e = parse_instance_call l read] ] -> e
    | [ [%l e = parse_instance_call_rest lf f [] target] ] -> e
    | [ ] -> read
    in
  function%parser
| [ (larrow, Kwd "->");
    [%l
    (lf, f, read) = begin function%parser
    | [ (lf, Ident f) ] -> lf, f, Read (larrow, target, f);
    | [ (_, Kwd "/*@"); 
      (_, Kwd "activating"); 
      (_, Kwd "@*/"); 
      (lf, Ident f) 
      ] -> lf, f, ActivatingRead (larrow, target, f)
    end
    ];
   [%l e = parse_call_or_read lf f [] target read]
  ] -> e
| [ (ldot, Kwd ".");
    [%l
    (lf, f, read) = begin function%parser
    | [ (lf, Ident f) ] -> lf, f, Select (ldot, target, f);
    | [ (_, Kwd "/*@"); 
        (_, Kwd "activating"); 
        (_, Kwd "@*/"); 
        (lf, Ident f) 
      ] -> lf, f, ActivatingRead (ldot, AddressOf (ldot, target), f)
    end
    ];
    [%l e = parse_call_or_read lf f [] (AddressOf (ldot, target)) read]
  ] -> e
and
  parse_expr_primary0 allowCast = fun stream -> stream |> function%parser
| [ (l, Kwd "true") ] -> True l
| [ (l, Kwd "false") ] -> False l
| [ (l, CharToken c) ] ->
  if Char.code c > 127 then raise (ParseException (l, "Non-ASCII character literals are not yet supported"));
  let tp = match language with CLang -> Int (Signed, CharRank) | Java -> Int (Unsigned, ShortRank) in
  CastExpr (l, ManifestTypeExpr (l, tp), IntLit (l, big_int_of_int (Char.code c), true, false, NoLSuffix))
| [ (l, Kwd "null") ] -> Null l
| [ (l, Kwd "currentThread") ] -> Var (l, "currentThread")
| [ (l, Kwd "varargs") ] -> Var (l, "varargs")
| [ (l, Kwd "new"); 
    parse_primary_type as tp; 
    [%l
    res = (function%parser 
    | [ parse_patlist as args0 ] -> 
        begin match tp with
          IdentTypeExpr(_, pac, cn) -> 
            NewObject (l, 
              (match pac with None -> "" | Some(pac) -> pac ^ ".") ^ cn, List.map (function LitPat e -> e | _ -> raise (Stream.Error "Patterns are not allowed in this position")) args0, None)
          | ConstructedTypeExpr(loc, name, targs) -> 
            NewObject (loc,
                name, List.map (function LitPat e -> e | _ -> raise (Stream.Error "Patterns are not allowed in this position")) args0,
                Some (targs))
          | _ -> raise (ParseException (type_expr_loc tp, "Class name expected"))
        end
    | [ [%l e = parse_new_array_expr_rest l tp] ] -> e
  )
  ]
  ] -> res
| [ (* TODO: parse type arguments for java generic methods *)
    (lx, Ident x);
    [%l
    ex = function%parser
    | [ parse_patlist as args0;
        [%l
        e = function%parser
        | [ parse_patlist as args ] -> CallExpr (lx, x, [], args0, args, Static)
        | [ ] -> CallExpr (lx, x, [], [], args0, Static)
        ]
      ] -> e
    | [ (ldot, Kwd ".");
        [%l targs = parse_type_args ldot];
        [%l
        r = function%parser
        | [ (lc, Kwd "class") ] -> ClassLit(ldot,x)
        | [ (lf, Ident f);
            [%l
            e = function%parser
            | [ [%l e = parse_instance_call_rest lf f targs (Var (lx, x))] ] -> e
            | [ ] -> Read (ldot, Var (lx, x), f)
            ]
          ] -> e 
        ]
      ] when language = Java -> r
    | [ [%l e = parse_instance_call lx (Var (lx, x))] ] -> e
    | [ ] -> Var (lx, x)
    ]
  ] when not (is_typedef x) || (match Stream.npeek 2 stream with [_; (_, Kwd ("("|"<"))] -> true | _ -> false) -> ex
| [ (l, Int (i, dec, usuffix, lsuffix, _)) ] -> IntLit (l, i, dec, usuffix, lsuffix)
| [ (l, RealToken i) ] -> RealLit (l, num_of_big_int i, None)
| [ (l, RationalToken (n, suffix)) ] -> RealLit (l, n, suffix)
| [ (l, Kwd "INT_MIN") ] -> (match int_width with LitWidth k -> IntLit (l, min_signed_big_int k, true, false, NoLSuffix) | IntWidth -> Operation (l, MinValue (Int (Signed, IntRank)), []))
| [ (l, Kwd "INT_MAX") ] -> (match int_width with LitWidth k -> IntLit (l, max_signed_big_int k, true, false, NoLSuffix) | IntWidth -> Operation (l, MaxValue (Int (Signed, IntRank)), []))
| [ (l, Kwd "UINTPTR_MAX") ] -> (match ptr_width with LitWidth k -> IntLit (l, max_unsigned_big_int k, true, true, NoLSuffix) | PtrWidth -> Operation (l, MaxValue (Int (Unsigned, PtrRank)), []))
| [ (l, Kwd "CHAR_MIN") ] -> IntLit (l, big_int_of_string "-128", true, false, NoLSuffix)
| [ (l, Kwd "CHAR_MAX") ] -> IntLit (l, big_int_of_string "127", true, false, NoLSuffix)
| [ (l, Kwd "UCHAR_MAX") ] -> IntLit (l, big_int_of_string "255", true, false, NoLSuffix)
| [ (l, Kwd "SHRT_MIN") ] -> IntLit (l, big_int_of_string "-32768", true, false, NoLSuffix)
| [ (l, Kwd "SHRT_MAX") ] -> IntLit (l, big_int_of_string "32767", true, false, NoLSuffix)
| [ (l, Kwd "USHRT_MAX") ] -> IntLit (l, big_int_of_string "65535", true, false, NoLSuffix)
| [ (l, Kwd "LONG_MIN") ] -> (match long_width with LitWidth k -> IntLit (l, min_signed_big_int k, true, false, NoLSuffix) | LongWidth -> Operation (l, MinValue (Int (Signed, LongRank)), []))
| [ (l, Kwd "LONG_MAX") ] -> (match long_width with LitWidth k -> IntLit (l, max_signed_big_int k, true, false, NoLSuffix) | LongWidth -> Operation (l, MaxValue (Int (Signed, LongRank)), []))
| [ (l, Kwd "ULONG_MAX") ] -> (match long_width with LitWidth k -> IntLit (l, max_unsigned_big_int k, true, true, NoLSuffix) | LongWidth -> Operation (l, MaxValue (Int (Unsigned, LongRank)), []))
| [ (l, Kwd "UINT_MAX") ] -> (match int_width with LitWidth k -> IntLit (l, max_unsigned_big_int k, true, true, NoLSuffix) | IntWidth -> Operation (l, MaxValue (Int (Unsigned, IntRank)), []))
| [ (l, Kwd "LLONG_MIN") ] -> IntLit (l, big_int_of_string "-9223372036854775808", true, false, LLSuffix)
| [ (l, Kwd "LLONG_MAX") ] -> IntLit (l, big_int_of_string "9223372036854775807", true, false, LLSuffix)
| [ (l, Kwd "ULLONG_MAX") ] -> IntLit (l, big_int_of_string "18446744073709551615", true, true, LLSuffix)
| [ (l, Kwd "__minvalue"); 
    (_, Kwd "("); 
    parse_type as te; 
    (_, Kwd ")") 
  ] -> (match te with ManifestTypeExpr (_, t) -> Operation (l, MinValue t, []))
| [ (l, Kwd "__maxvalue"); 
    (_, Kwd "("); 
    parse_type as te; 
    (_, Kwd ")") 
  ] -> (match te with ManifestTypeExpr (_, t) -> Operation (l, MaxValue t, []))
| [ (l, String s); 
    [%l
    ss = rep (function%parser 
    | [ (_, String s) ] -> s
    ) 
    ]
  ] -> 
    let s = String.concat "" (s::ss) in
    StringLit (l, s)
| [ (l, Kwd "(");
    [%l
    e =
      let parse_cast = function%parser 
      | [ parse_type as te; 
          (_, Kwd ")"); 
          [%l
          e = 
            if allowCast then 
              (function%parser [ parse_expr_suffix as e ] -> CastExpr (l, te, e) | [ ] -> TypeExpr te) 
            else 
              (function%parser [ ] -> TypeExpr te) 
          ]
        ] -> e 
      in
      let parse_expr_rest e0 = function%parser
      | [ (l', Ident y); 
          [%l e = parse_expr_suffix_rest (Var (l', y))] 
        ] ->
          begin match e0 with
          (* This isn't quite right I think, but I really can't figure out another way to allow casts of paramterised types *)
          | CallExpr (lt, x, targs, [], [], Static) -> CastExpr (l, ConstructedTypeExpr(lt, x, targs), e)
          | Var (lt, x) -> CastExpr (l, IdentTypeExpr (lt, None, x), e)
          | _ -> raise (ParseException (l, "Type expression of cast expression must be identifier: "))
          end
      | [ ] -> e0
      in
      let parse =
        function%parser
        | [ parse_expr as e0; 
            (_, Kwd ")"); 
            [%l e = parse_expr_rest e0] 
          ] -> e
        | [ parse_cast as e ] -> e
      in
      begin fun stream -> 
        match Stream.peek stream with
          Some (_, Ident x) when is_typedef x -> parse_cast stream
        | _ -> parse stream
      end
    ]
  ] -> e
(*
| [< '(l, Kwd "(");
     e = parser
     [< e = parse_expr; '(_, Kwd ")") >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e*)
| [ (l, Kwd "switch"); 
    (_, Kwd "("); 
    parse_expr as e; 
    (_, Kwd ")"); 
    (_, Kwd "{"); 
    parse_switch_expr_clauses as cs;
    [%l
    cdef_opt = opt (function%parser 
    | [ (l, Kwd "default"); 
        (_, Kwd ":"); 
        (_, Kwd "return"); 
        parse_expr as e; 
        (_, Kwd ";") 
      ] -> (l, e)
    )
    ];
    (_, Kwd "}")
  ] -> SwitchExpr (l, e, cs, cdef_opt)
| [ (l, Kwd "sizeof"); [%l e = parse_expr_suffix0 false] ] -> SizeofExpr (l, e)
| [ (l, Kwd "typeid"); 
    (_, Kwd "("); 
    parse_type as te; 
    (_, Kwd ")") 
  ] when language <> Java -> Typeid (l, TypeExpr te)
| [ (l, Kwd "super"); 
    (_, Kwd "."); 
    (l2, Ident n); 
    (_, Kwd "("); 
    [%l es = rep_comma parse_expr]; 
    (_, Kwd ")") 
  ] -> SuperMethodCall (l, n, es)
| [ (l, Kwd "!"); 
    parse_expr_suffix as e 
  ] -> Operation(l, Not, [e])
| [ (l, Kwd "@"); 
    (_, Ident g) 
  ] -> PredNameExpr (l, g)
| [ (l, Kwd "*"); 
    parse_expr_suffix as e 
  ] -> Deref (l, e)
| [ (l, Kwd "&"); 
    parse_expr_suffix as e 
  ] -> AddressOf (l, e)
| [ (l, Kwd "~"); 
    parse_expr_suffix as e 
  ] -> Operation (l, BitNot, [e])
| [ (l, Kwd "-"); 
    parse_expr_suffix as e 
  ] ->
  begin match e with
    IntLit (_, n, true, false, lsuffix) when language = Java && sign_big_int n >= 0 -> IntLit (l, minus_big_int n, true, false, lsuffix)
  | _ -> Operation (l, Sub, [IntLit (l, zero_big_int, true, false, NoLSuffix); e])
  end
| [ (l, Kwd "++"); parse_expr_suffix as e ] -> AssignOpExpr (l, e, Add, IntLit (l, unit_big_int, true, false, NoLSuffix), false)
| [ (l, Kwd "--"); parse_expr_suffix as e ] -> AssignOpExpr (l, e, Sub, IntLit (l, unit_big_int, true, false, NoLSuffix), false)
| [ (l, Kwd "{"); [%l es = rep_comma parse_expr]; (_, Kwd "}") ] -> InitializerList (l, es)
| [ (l, Kwd "_Generic"); 
    (_, Kwd "("); 
    parse_expr as e; 
    [%l (cs, d) = parse_generic_cases l]; 
    (_, Kwd ")") 
  ] -> GenericExpr (l, e, cs, d)
| [ parse_asn0 as a ] -> a
and
  parse_generic_cases l = function%parser
| [ (_, Kwd ","); 
    [%l
    (cs, d) = begin function%parser
    | [ (_, Kwd "default"); 
        (_, Kwd ":"); 
        parse_expr as e; 
        [%l (cs, d) = parse_generic_cases l] 
      ] ->
        begin match d with
          Some e -> raise (ParseException (l, "A _Generic expression must not have multiple default clauses"))
        | None -> (cs, Some e)
        end
    | [ parse_type as te; 
        (_, Kwd ":");
        parse_expr as e; 
        [%l (cs, d) = parse_generic_cases l] 
      ] -> ((te, e)::cs, d)
    end 
    ]
  ] -> (cs, d)
| [ ] -> ([], None)
and
  parse_switch_expr_clauses = function%parser
| [ parse_switch_expr_clause as c; parse_switch_expr_clauses as cs ] -> c::cs
| [ ] -> []
and
  parse_switch_expr_clause = function%parser
| [ (l, Kwd "case"); 
    (_, Ident c); 
    [%l
    pats = (function%parser 
    | [ (_, Kwd "("); 
        (lx, Ident x); 
        [%l () = (fun _ -> register_varname x)]; 
        parse_more_pats as xs 
      ] -> x::xs 
    | [ ] -> []
    )
    ]; 
    (_, Kwd ":"); 
    (_, Kwd "return"); 
    parse_expr as e; 
    (_, Kwd ";") 
  ] -> SwitchExprClause (l, c, pats, e)
and
  expr_to_class_name e =
    match e with
      Var (_, x) -> x
    | Read (_, e, f) -> expr_to_class_name e ^ "." ^ f
    | _ -> raise (ParseException (expr_loc e, "Class name expected"))
and
  parse_expr_suffix_rest e0 = function%parser
  [ (l, Kwd "->");
    [%l
    e = begin function%parser
    | [ (_, Ident f); 
        [%l e = parse_expr_suffix_rest (Read (l, e0, f))] 
      ] -> e
    | [ (_, Kwd "/*@"); 
        (_, Kwd "activating"); 
        (_, Kwd "@*/"); 
        (_, Ident f); 
        [%l e = parse_expr_suffix_rest (ActivatingRead (l, e0, f))]
      ] -> e
    end 
    ]
  ] -> e
| [ (l, Kwd ".");
    [%l
    e = begin function%parser
    | [ (_, Ident f); 
        [%l e = parse_expr_suffix_rest (Select (l, e0, f))] 
      ] -> e
    | [ (_, Kwd "/*@"); 
        (_, Kwd "activating"); 
        (_, Kwd "@*/"); 
        (_, Ident f); 
        [%l e = parse_expr_suffix_rest (ActivatingRead (l, AddressOf (l, e0), f))] 
      ] -> e
    end 
    ]
  ] when language = CLang -> e
| [ (l, Kwd ".");
    [%l
    e = begin function%parser
    | [ (_, Ident f); 
        [%l e = parse_expr_suffix_rest (Read (l, e0, f))]
      ] -> e
    | [ (_, Kwd "class"); 
        [%l e = parse_expr_suffix_rest (ClassLit (l, expr_to_class_name e0))]
      ] -> e
    end
    ]
  ] -> e
| [ (l, Kwd "["); 
    [%l
    e = begin function%parser
    | [ (_, Kwd "]") ] -> ArrayTypeExpr' (l, e0)
    | [ [%l p1 = opt parse_pattern];
        [%l
        e = begin function%parser
        | [ (ls, Kwd ".."); 
            [%l p2 = opt parse_pattern]; 
            (_, Kwd "]") 
          ] -> ReadArray (l, e0, SliceExpr (ls, p1, p2))
        | [ (_, Kwd "]") ] -> begin match p1 with Some (LitPat e1) -> ReadArray (l, e0, e1) | _ -> raise (ParseException (l, "Malformed array access.")) end
        end
        ]
      ] -> e
     end
    ]; 
    [%l e = parse_expr_suffix_rest e] 
  ] -> e
| [ (l, Kwd "++"); 
    [%l e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Add, IntLit (l, unit_big_int, true, false, NoLSuffix), true))] ] -> e
| [ (l, Kwd "--"); 
    [%l e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Sub, IntLit (l, unit_big_int, true, false, NoLSuffix), true))] ] -> e
| [ (l, Kwd "("); 
    [%l es = rep_comma parse_expr]; 
    (_, Kwd ")"); 
    [%l e = parse_expr_suffix_rest (match e0 with Read(l', e0', f') -> CallExpr (l', f', [], [], LitPat(e0'):: (List.map (fun e -> LitPat(e)) es), Instance) | _ -> ExprCallExpr (l, e0, es))]
  ] -> e
| [ ] -> e0
and
  parse_expr_mul_rest e0 = function%parser
| [ (l, Kwd "*"); 
    parse_expr_suffix as e1; 
    [%l e = parse_expr_mul_rest (Operation (l, Mul, [e0; e1]))] 
  ] -> e
| [ (l, Kwd "/"); 
    parse_expr_suffix as e1; 
    [%l e = parse_expr_mul_rest (Operation (l, Div, [e0; e1]))]
  ] -> e
| [ (l, Kwd "%"); 
    parse_expr_suffix as e1; 
    [%l e = parse_expr_mul_rest (Operation (l, Mod, [e0; e1]))] 
  ] -> e
| [ ] -> e0
and
  parse_expr_arith_rest e0 = function%parser
| [ (l, Kwd "+"); 
    parse_expr_mul as e1; 
    [%l e = parse_expr_arith_rest (Operation (l, Add, [e0; e1]))] 
  ] -> e
| [ (l, Kwd "-"); 
    parse_expr_mul as e1; 
    [%l e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1]))] 
  ] -> e
| [ ] -> e0
and
  parse_shift_rest e0 = function%parser
| [ (l, Kwd "<<"); parse_expr_arith as e1; [%l e = parse_shift_rest (Operation (l, ShiftLeft, [e0; e1]))] ] -> e
| [ (l, Kwd ">>"); parse_expr_arith as e1; [%l e = parse_shift_rest (Operation (l, ShiftRight, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_expr_rel_rest e0 = function%parser
| [ (l, Kwd "=="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1]))] ] -> e
| [ (l, Kwd "!="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1]))] ] -> e
| [ (l, Kwd "<="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Le, [e0; e1]))] ] -> e
| [ (l, Kwd ">"); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Gt, [e0; e1]))] ] -> e
| [ (l, Kwd ">="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Ge, [e0; e1]))] ] -> e
| [ (l, Kwd "instanceof"); parse_expr as tp; [%l e = parse_expr_rel_rest (InstanceOfExpr (l, e0, type_expr_of_expr tp))] ] -> e
| [ [%l e = parse_expr_lt_rest e0 parse_expr_rel_rest] ] -> e
and
  apply_type_args e targs args =
  match e with
    Var (lx, x) -> CallExpr (lx, x, targs, [], args, Static)
  | CastExpr (lc, te, e) -> CastExpr (lc, te, apply_type_args e targs args)
  | Operation (l, Not, [e]) -> Operation (l, Not, [apply_type_args e targs args])
  | Operation (l, BitNot, [e]) -> Operation (l, BitNot, [apply_type_args e targs args])
  | Deref (l, e) -> Deref (l, apply_type_args e targs args)
  | AddressOf (l, e) -> AddressOf (l, apply_type_args e targs args)
  | Operation (l, op, [e1; e2]) -> Operation (l, op, [e1; apply_type_args e2 targs args])
  | _ -> raise (ParseException (expr_loc e, "Identifier expected before type argument list"))
and
  parse_expr_lt_rest e0 cont = function%parser
| [ (l, Kwd "<");
    [%l
    e = function%parser
    | [ parse_truncating_expr as e1; 
        [%l e1 = parse_expr_lt_rest e1 (let rec iter e0 = parse_expr_lt_rest e0 iter in iter)];
        [%l
        e = function%parser
        | [ (_, Kwd ">"); (* Type argument *)
            [%l args = (function%parser [ parse_patlist as args ] -> args | [ ] -> [])];
            [%l e = cont (apply_type_args e0 [type_expr_of_expr e1] args)]
          ] -> e
        | [ (_, Kwd ","); 
            [%l ts = rep_comma parse_type]; 
            (_, Kwd ">");
            [%l args = (function%parser [ parse_patlist as args ] -> args | [ ] -> [])];
            [%l e = cont (apply_type_args e0 ([type_expr_of_expr e1] @ ts) args)]
          ] -> e
        | [ [%l e = cont (Operation (l, Lt, [e0; e1]))] ] -> e
        ]
      ] -> e
    | [ [%l ts = rep_comma parse_type]; 
        (_, Kwd ">");
        [%l args = (function%parser [ parse_patlist as args ] -> args | [ ] -> [])];
        [%l e = cont (apply_type_args e0 ts args)]
      ] -> e
    ]
  ] -> e
| [ ] -> e0
and
  parse_bitand_expr_rest e0 = function%parser
| [ (l, Kwd "&"); parse_expr_rel as e1; [%l e = parse_bitand_expr_rest (Operation (l, BitAnd, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_bitxor_expr_rest e0 = function%parser
| [ (l, Kwd "^"); parse_bitand_expr as e1; [%l e = parse_bitxor_expr_rest (Operation (l, BitXor, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_bitor_expr_rest e0 = function%parser
| [ (l, Kwd "|"); parse_bitxor_expr as e1; [%l e = parse_bitor_expr_rest (Operation (l, BitOr, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_conj_expr_rest e0 = function%parser
| [ (l, Kwd "&&"); parse_bitor_expr as e1; [%l e = parse_conj_expr_rest (Operation (l, And, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_disj_expr_rest e0 = function%parser
| [ (l, Kwd "||"); parse_conj_expr as e1; [%l e = parse_disj_expr_rest (Operation (l, Or, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_assign_expr_rest e0 = function%parser
| [ (l, Kwd "="); parse_assign_expr as e1 ] -> AssignExpr (l, e0, e1)
| [ (l, Kwd "+="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, Add, e1, false)
| [ (l, Kwd "-="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, Sub, e1, false)
| [ (l, Kwd "*="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, Mul, e1, false)
| [ (l, Kwd "/="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, Div, e1, false)
| [ (l, Kwd "&="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, BitAnd, e1, false)
| [ (l, Kwd "|="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, BitOr, e1, false)
| [ (l, Kwd "^="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, BitXor, e1, false)
| [ (l, Kwd "%="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, Mod, e1, false)
| [ (l, Kwd "<<="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, ShiftLeft, e1, false)
| [ (l, Kwd ">>="); parse_assign_expr as e1 ] -> AssignOpExpr (l, e0, ShiftRight, e1, false)
(*| [< '(l, Kwd ">>>="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ???, e1, false)*)
| [ ] -> e0
and
  parse_arglist = function%parser
| [ (l, Kwd "("); 
    [%l
    es = function%parser 
    | [ (_, Kwd ")") ] -> [] 
    | [ parse_expr as e0; 
        parse_arglist_rest as es 
      ] -> e0::es 
    ]
  ] -> es
and
  parse_arglist_rest = function%parser
| [ (_, Kwd ","); parse_expr as e0; parse_arglist_rest as es ] -> e0::es
| [ (_, Kwd ")") ] -> []
and
  parse_patlist = function%parser
| [ (l, Kwd "("); 
    [%l
    pats = function%parser 
    | [ (_, Kwd ")") ] -> [] 
    | [ parse_pattern as pat0; parse_patlist_rest as pats ] -> pat0::pats 
    ]
  ] -> pats
and
  parse_patlist_rest = function%parser
| [ (_, Kwd ","); parse_pattern as pat0; parse_patlist_rest as pats ] -> pat0::pats
| [ (_, Kwd ")") ] -> []

end

let parse_decls lang dataModel enforceAnnotations ?inGhostHeader =
  let module MyParserArgs = struct
    let language = lang
    let enforce_annotations = enforceAnnotations
    let data_model = dataModel
  end in
  let module MyParser = Parser(MyParserArgs) in
  MyParser.parse_decls ?inGhostHeader

let rec parse_package_name = function%parser
  [ (_, Ident n); 
    [%l
    x = function%parser
    | [ (_, Kwd ".");
      parse_package_name as rest
      ] -> n ^ "." ^ rest
    | [(_, Kwd ";") ] -> n
    ]
  ] -> x
  
let parse_package = function%parser
  [ (l, Kwd "package"); parse_package_name as n ] ->(l,n)
| [ ] -> (dummy_loc,"")
  
let rec parse_import_names = function%parser
  [ (_, Kwd "."); 
    [%l
    y = function%parser
    | [ (_, Kwd "*"); (_, Kwd ";") ] -> ("", None)
    | [ (_, Ident el);
        [%l 
        x = function%parser
        | [ (_, Kwd ";") ]-> ("", Some el)
        | [ parse_import_names as rest ] -> let (n',el') = rest in ("." ^el^n',el')
        ]
      ] -> x
    ]
  ] -> y

let parse_import_name = function%parser
| [ (_, Ident n); [%l (n',el) = parse_import_names] ] -> (n^n',el)
  
let parse_import0 = function%parser
  [ (l, Kwd "import"); parse_import_name as n ] -> let (pn,el)=n in Import(l,Real,pn,el)

let parse_import = function%parser
| [ parse_import0 as i ] -> i
| [ [%l i = peek_in_ghost_range (function%parser [ parse_import0 as i; (_, Kwd "@*/") ] -> i)] ] ->
    (match i with Import(l, Real, pn,el) -> Import(l, Ghost, pn,el))

let parse_package_decl enforceAnnotations = function%parser
| [ [%l (l,p) = parse_package]; [%l is=rep parse_import]; [%l ds=parse_decls Java (Some data_model_java) enforceAnnotations]; ] -> PackageDecl(l,p,Import(dummy_loc,Real,"java.lang",None)::is, ds)

let noop_preprocessor stream =
  let next _ =
    let result = Stream.peek stream in
    match result with
      None -> None
    | Some (l, t) ->
      Stream.junk stream;
      Some (Lexed l, t)
  in
  Stream.from next

let parse_scala_file (path: string) (reportRange: range_kind -> loc0 -> unit): package =
  let lexer = make_lexer Scala.keywords ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer path (readFile path) reportRange (fun _ _ -> ()) in
  let parse_decls_eof = function%parser [ [%l ds = rep Scala.parse_decl]; (_, Eof) ] -> PackageDecl(dummy_loc,"",[Import(dummy_loc,Real,"java.lang",None)],ds) in
  try
    parse_decls_eof (noop_preprocessor token_stream)
  with
    Stream.Error msg -> raise (ParseException (Lexed (loc()), msg))
  | Stream.Failure -> raise (ParseException (Lexed (loc()), "Parse error"))

(*
  old way to parse java files, these files (including non-run-time javaspec files)
  can now be handled by the Java frontend
*)
let parse_java_file_old (path: string) (reportRange: range_kind -> loc0 -> unit) reportShouldFail verbose enforceAnnotations: package =
  Stopwatch.start parsing_stopwatch;
  if verbose = -1 then Printf.printf "%10.6fs: >> parsing Java file: %s \n" (Perf.time()) path;
  let result =
  if Filename.check_suffix (Filename.basename path) ".scala" then
    parse_scala_file path reportRange
  else
  let lexer = make_lexer (common_keywords @ java_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer path (readFile path) reportRange reportShouldFail in
  let parse_decls_eof = function%parser [ [%l p = parse_package_decl enforceAnnotations]; (_, Eof) ] -> p in
  try
    parse_decls_eof (noop_preprocessor token_stream)
  with
    Stream.Error msg -> raise (ParseException (Lexed (loc()), msg))
  | Stream.Failure -> raise (ParseException (Lexed (loc()), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

type 'result parser_ = (loc * token) Stream.t -> 'result

let rec parse_include_directives_core (verbose: int) (enforceAnnotations: bool) (dataModel: data_model option) (active_headers: string list ref): 
    ((loc * (include_kind * string * string) * string list * package list) list * string list) parser_ =
  let test_include_cycle l totalPath =
    if List.mem totalPath !active_headers then raise (ParseException (l, "Include cycles (even with header guards) are not supported"));
  in
  let rec parse_include_directives_core header_names in_ghost_range =
    let parse = function%parser
      | [ (_, Kwd "/*@"); 
          [%l (headers, header_name) = parse_include_directive true]; 
          [%l (headers', header_names') = parse_include_directives_core (header_name::header_names) true] 
        ] -> (List.append headers headers', header_names')
      | [ [%l (headers, header_name) = parse_include_directive in_ghost_range]; 
          [%l (headers', header_names') = parse_include_directives_core (header_name::header_names) in_ghost_range] 
        ] -> (List.append headers headers', header_names')
      | [ (_, Kwd "@*/"); 
          [%l (headers', header_names') = parse_include_directives_core header_names false] 
        ] -> headers', header_names'
    in
    begin fun stream ->
      begin match Stream.npeek 2 stream with
      | [(_, Kwd "/*@"); (_, BeginInclude (_, _, _)) | (_, SecondaryInclude (_, _))] when not in_ghost_range ->
        parse stream
      | [(_, BeginInclude (_, _, _)) | (_, SecondaryInclude (_, _)); _] ->
        parse stream
      | [(_, Kwd "@*/"); _] when in_ghost_range ->
        parse stream
      | [(_, Kwd "/*@"); (_, Kwd "@*/")] when not in_ghost_range ->
        begin
          Stream.junk stream;
          Stream.junk stream;
          parse_include_directives_core header_names false stream
        end
      | _ -> 
        [], header_names
      end
    end
  and parse_include_directive in_ghost_range = 
    let isGhostHeader header = Filename.check_suffix header ".gh" in
    function%parser
    | [ (l, SecondaryInclude(h, totalPath)) ] -> 
        if verbose = -1 then Printf.printf "%10.6fs: >>>> ignored secondary include: %s \n" (Perf.time()) totalPath;
        test_include_cycle l totalPath; ([], totalPath)
    | [ (l, BeginInclude(kind, h, totalPath)); 
        [%l (headers, header_names) = (active_headers := totalPath::!active_headers; parse_include_directives_core [] in_ghost_range)]; 
        [%l ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:(isGhostHeader h)]; 
        (_, Eof); 
        (_, EndInclude) 
      ] ->
        if verbose = -1 then Printf.printf "%10.6fs: >>>> parsed include: %s \n" (Perf.time()) totalPath;
        active_headers := List.filter (fun h -> h <> totalPath) !active_headers;
        let ps = [PackageDecl(dummy_loc,"",[],ds)] in
        (List.append headers [(l, (kind, h, totalPath), header_names, ps)], totalPath)
  in
  parse_include_directives_core [] false

let rec parse_include_directives (verbose: int) (enforceAnnotations: bool) (dataModel: data_model option): 
  ((loc * (include_kind * string * string) * string list * package list) list * string list) parser_ =
  let active_headers = ref [] in
  parse_include_directives_core verbose enforceAnnotations dataModel active_headers

let parse_c_file reportMacroCall (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: string -> loc0 -> unit) (verbose: int) 
            (include_paths: string list) (define_macros: string list) (enforceAnnotations: bool) (dataModel: data_model option): ((loc * (include_kind * string * string) * string list * package list) list * package list) = (* ?parse_c_file *)
  Stopwatch.start parsing_stopwatch;
  if verbose = -1 then Printf.printf "%10.6fs: >> parsing C file: %s \n" (Perf.time()) path;
  let result =
    let make_lexer path include_paths ~inGhostRange =
      let text = readFile path in
      make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange reportShouldFail
    in
    let (loc, token_stream) = make_preprocessor reportMacroCall make_lexer path verbose include_paths dataModel define_macros in
    let parse_c_file =
      function%parser
      | [ [%l (headers, _d) = parse_include_directives verbose enforceAnnotations dataModel]; 
          [%l ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:false]; 
          (_, Eof) 
        ] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
    in
    try
      parse_c_file token_stream
    with
      Stream.Error msg -> raise (ParseException (loc(), msg))
    | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

let parse_header_file reportMacroCall (path: string) (reportRange: range_kind -> loc0 -> unit) (reportShouldFail: string -> loc0 -> unit) (verbose: int) 
         (include_paths: string list) (define_macros: string list) (enforceAnnotations: bool) (dataModel: data_model option): ((loc * (include_kind * string * string) * string list * package list) list * package list) =
  Stopwatch.start parsing_stopwatch;
  if verbose = -1 then Printf.printf "%10.6fs: >> parsing Header file: %s \n" (Perf.time()) path;
  let isGhostHeader = Filename.check_suffix path ".gh" in
  let result =
    let make_lexer path include_paths ~inGhostRange =
      let text = readFile path in
      make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange:inGhostRange reportShouldFail
    in
    let (loc, token_stream) = make_preprocessor reportMacroCall make_lexer path verbose include_paths dataModel define_macros in
    let p = function%parser
    | [ [%l (headers, _d) = parse_include_directives verbose enforceAnnotations dataModel]; 
        [%l ds = parse_decls CLang dataModel enforceAnnotations ~inGhostHeader:isGhostHeader]; 
        (_, Eof)
      ] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
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
  let pos = (path, 1, 1) in
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

let path_macros = [("VERIFAST", rtdir())]

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
  (* Filter comments *)
  let lines = List.filter (fun x -> if (String.contains x '#') then not (String.index x '#' == 0) else true) lines in
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
          raise (ParseException (Lexed (file_loc path), "A .jarspec file must consists of a list of .jarspec file paths followed by a list of .javaspec file paths"))
        else
          [line]
      end
      lines
  in
  (jarspecs, javaspecs)

(* Returned paths are relative to the directory of [path] *)
let parse_jarsrc_file_core path =
  let lines = read_file_lines path in
  (* Filter comments *)
  let lines = List.filter (fun x -> if (String.contains x '#') then not (String.index x '#' == 0) else true) lines in
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
      provides @ [(Util.concat !Util.bindir "main_class ") ^ mainClass]
    | _ ->
      raise (ParseException (Lexed (file_loc path), "A .jarsrc file must consists of a list of .jar file paths followed by a list of .java file paths, optionally followed by a line of the form \"main-class mymainpackage.MyMainClass\""))
  in
  (jars, javas, provides)
