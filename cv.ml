module CVerifier =
struct

let verbose = ref false

let verbose_print_endline s = if !verbose then print_endline s else ()
let verbose_print_string s = if !verbose then print_string s else ()

type token =
    Kwd of string
  | Ident of string
  | Int of int
  | Float of float
  | String of string
  | Char of char

(* The lexer *)

let make_lexer keywords stream =
  let initial_buffer = String.create 32
  in

  let buffer = ref initial_buffer
  in
  let bufpos = ref 0
  in

  let reset_buffer () = buffer := initial_buffer; bufpos := 0
  in

  let store c =
    if !bufpos >= String.length !buffer then
      begin
        let newbuffer = String.create (2 * !bufpos) in
        String.blit !buffer 0 newbuffer 0 !bufpos; buffer := newbuffer
      end;
    String.set !buffer !bufpos c;
    incr bufpos
  in

  let get_string () =
    let s = String.sub !buffer 0 !bufpos in buffer := initial_buffer; s
  in

  let line = ref 1 in
  let linepos = ref 0 in  (* Stream count at start of line *)
  let tokenpos = ref 0 in

  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  let ident_or_keyword id =
    try Hashtbl.find kwd_table id with
      Not_found -> Ident id
  and keyword_or_error c =
    let s = String.make 1 c in
    try Hashtbl.find kwd_table s with
      Not_found -> raise (Stream.Error ("Illegal character " ^ s))
  in
  let start_token() = tokenpos := Stream.count stream in
  let rec next_token (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some (' ' | '\009' | '\026' | '\012') ->
        Stream.junk strm__; next_token strm__
    | Some '\010' ->
        Stream.junk strm__; line := !line + 1; linepos := Stream.count strm__; next_token strm__
    | Some '\013' ->
        Stream.junk strm__;
        if Stream.peek strm__ = Some '\010' then Stream.junk strm__;
        line := !line + 1; linepos := Stream.count strm__;
        next_token strm__
    | Some ('A'..'Z' | 'a'..'z' | '_' | '\192'..'\255' as c) ->
        start_token();
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); store c; ident s
    | Some
        ('!' | '%' | '&' | '$' | '#' | '+' | '(' | ':' | '<' | '=' | '>' |
         '?' | '@' | '\\' | '~' | '^' | '|' | '*' as c) ->
        start_token();
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); store c; ident2 s
    | Some ('0'..'9' as c) ->
        start_token();
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); store c; number s
    | Some '\'' ->
        start_token();
        Stream.junk strm__;
        let c =
          try char strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        begin match Stream.peek strm__ with
          Some '\'' -> Stream.junk strm__; Some (Char c)
        | _ -> raise (Stream.Error "")
        end
    | Some '"' ->
        start_token();
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); Some (String (string s))
    | Some '-' -> start_token(); Stream.junk strm__; neg_number strm__
    | Some '/' -> start_token(); Stream.junk strm__; maybe_comment strm__
    | Some c -> start_token(); Stream.junk strm__; Some (keyword_or_error c)
    | _ -> None
  and ident (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some
        ('A'..'Z' | 'a'..'z' | '\192'..'\255' | '0'..'9' | '_' | '\'' as c) ->
        Stream.junk strm__; let s = strm__ in store c; ident s
    | _ -> Some (ident_or_keyword (get_string ()))
  and ident2 (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some
        ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' |
         '>' | '?' | '@' | '\\' | '~' | '^' | '|' | '*' as c) ->
        Stream.junk strm__; let s = strm__ in store c; ident2 s
    | _ -> Some (ident_or_keyword (get_string ()))
  and neg_number (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('0'..'9' as c) ->
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); store '-'; store c; number s
    | _ -> let s = strm__ in reset_buffer (); store '-'; ident2 s
  and number (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('0'..'9' as c) ->
        Stream.junk strm__; let s = strm__ in store c; number s
    | Some '.' ->
        Stream.junk strm__; let s = strm__ in store '.'; decimal_part s
    | Some ('e' | 'E') ->
        Stream.junk strm__; let s = strm__ in store 'E'; exponent_part s
    | _ -> Some (Int (int_of_string (get_string ())))
  and decimal_part (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('0'..'9' as c) ->
        Stream.junk strm__; let s = strm__ in store c; decimal_part s
    | Some ('e' | 'E') ->
        Stream.junk strm__; let s = strm__ in store 'E'; exponent_part s
    | _ -> Some (Float (float_of_string (get_string ())))
  and exponent_part (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('+' | '-' as c) ->
        Stream.junk strm__; let s = strm__ in store c; end_exponent_part s
    | _ -> end_exponent_part strm__
  and end_exponent_part (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('0'..'9' as c) ->
        Stream.junk strm__; let s = strm__ in store c; end_exponent_part s
    | _ -> Some (Float (float_of_string (get_string ())))
  and string (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '"' -> Stream.junk strm__; get_string ()
    | Some '\\' ->
        Stream.junk strm__;
        let c =
          try escape strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        let s = strm__ in store c; string s
    | Some c -> Stream.junk strm__; let s = strm__ in store c; string s
    | _ -> raise Stream.Failure
  and char (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\\' ->
        Stream.junk strm__;
        begin try escape strm__ with
          Stream.Failure -> raise (Stream.Error "")
        end
    | Some c -> Stream.junk strm__; c
    | _ -> raise Stream.Failure
  and escape (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some 'n' -> Stream.junk strm__; '\n'
    | Some 'r' -> Stream.junk strm__; '\r'
    | Some 't' -> Stream.junk strm__; '\t'
    | Some ('0'..'9' as c1) ->
        Stream.junk strm__;
        begin match Stream.peek strm__ with
          Some ('0'..'9' as c2) ->
            Stream.junk strm__;
            begin match Stream.peek strm__ with
              Some ('0'..'9' as c3) ->
                Stream.junk strm__;
                Char.chr
                  ((Char.code c1 - 48) * 100 + (Char.code c2 - 48) * 10 +
                     (Char.code c3 - 48))
            | _ -> raise (Stream.Error "")
            end
        | _ -> raise (Stream.Error "")
        end
    | Some c -> Stream.junk strm__; c
    | _ -> raise Stream.Failure
  and maybe_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '/' ->
        Stream.junk strm__; let s = strm__ in comment s; next_token s
    | _ -> Some (keyword_or_error '/')
  and comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '@' -> Stream.junk strm__
    | Some '\010' | Some '\013' -> ()
    | Some c -> Stream.junk strm__; comment strm__
    | _ -> raise Stream.Failure
  in
  ((fun () -> (!line, Stream.count stream - !linepos + 1)), Stream.from (fun count -> (match next_token stream with Some t -> Some ((!line, !tokenpos - !linepos + 1), t) | None -> None)))

type
  operator = string
and
  loc = (int * int)
and
  expr =
    Var of loc * string
  | Operation of loc * operator * expr list
  | Read of loc * expr * string
  | CallExpr of loc * string * expr list
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of loc * expr * switch_expr_clause list
  | SizeofExpr of loc * type_expr
  | TypeExpr of loc * type_expr
and
  switch_expr_clause =
    SwitchExprClause of loc * string * string list * expr
and
  stmt =
    Assign of loc * string * expr
  | DeclStmt of loc * type_expr * string * expr
  | Write of loc * expr * string * expr
  | CallStmt of loc * string * expr list
  | IfStmt of loc * expr * stmt list * stmt list
  | SwitchStmt of loc * expr * switch_stmt_clause list
  | Open of loc * string * expr list
  | Close of loc * string * expr list
  | ReturnStmt of loc * expr option
  | WhileStmt of loc * expr * pred * stmt list
and
  switch_stmt_clause =
  | SwitchStmtClause of loc * string * string list * stmt list
and
  pred =
    Access of loc * expr * string * expr
  | CallPred of loc * string * expr list
  | ExprPred of loc * expr
  | Sep of loc * pred * pred
  | IfPred of loc * expr * pred * pred
  | SwitchPred of loc * expr * switch_pred_clause list
  | EmpPred of loc
and
  switch_pred_clause =
  | SwitchPredClause of loc * string * string list * pred
and
  func_kind =
  | Regular
  | Fixpoint
  | Lemma
and
  decl =
  | Inductive of loc * string * ctor list
  | Struct of loc * string * field list
  | PredDecl of loc * string * (type_expr * string) list * pred
  | Func of loc * func_kind * type_expr option * string * (type_expr * string) list * (pred * pred) option * stmt list
and
  field =
  | Field of loc * type_expr * string
and
  ctor =
  | Ctor of loc * string * type_expr list
and
  type_expr =
  | TypeName of loc * string
  | PtrType of loc * string   (* Always pointer-to-struct for now. *)
and
  program =
    Program of decl list

let string_of_loc (l,c) = "(" ^ string_of_int l ^ ":" ^ string_of_int c ^ ")"

let expr_loc e =
  match e with
    Var (l, x) -> l
  | Operation (l, op, es) -> l
  | Read (l, e, f) -> l
  | CallExpr (l, g, es) -> l
  | IfExpr (l, e1, e2, e3) -> l
  | SwitchExpr (l, e, secs) -> l
  | SizeofExpr (l, t) -> l
  | TypeExpr (l, t) -> l

let pred_loc p =
  match p with
    Access (l, e, f, rhs) -> l
  | CallPred (l, g, es) -> l
  | ExprPred (l, e) -> l
  | Sep (l, p1, p2) -> l
  | IfPred (l, e, p1, p2) -> l
  | SwitchPred (l, e, spcs) -> l
  | EmpPred l -> l

let type_loc t =
  match t with
    TypeName (l, n) -> l
  | PtrType (l, n) -> l

let lexer = make_lexer [
  "struct"; "{"; "}"; "*"; ";"; "int"; "predicate"; "("; ")"; ","; "requires";
  "->"; "|->"; "&*&"; "inductive"; "="; "|"; "fixpoint"; "switch"; "case"; ":";
  "return"; "+"; "=="; "?"; "true"; "ensures"; "sizeof"; "close"; "void"; "lemma";
  "open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; "<="
]

let read_program s =
  let c = open_in s in
  let (loc, token_stream) = lexer (Stream.of_channel c) in
let rec parse_program = parser
  [< ds = parse_decls; _ = Stream.empty >] -> Program ds
and
  parse_decls = parser
  [< d = parse_decl; ds = parse_decls >] -> d::ds
and
  parse_decl = parser
  [< '(l, Kwd "inductive"); '(_, Ident i); '(_, Kwd "="); cs = parse_ctors; '(_, Kwd ";") >] -> Inductive (l, i, cs)
| [< '(l, Kwd "struct"); '(_, Ident s); '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, fs)
| [< '(l, Kwd "predicate"); '(_, Ident g); ps = parse_paramlist; '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";") >] -> PredDecl (l, g, ps, p)
| [< k = parse_func_kind; t = parse_return_type; '(l, Ident g); ps = parse_paramlist; co = parse_contract_opt; ss = parse_block >] -> Func (l, k, t, g, ps, co, ss)
and
  parse_ctors = parser
  [< '(_, Kwd "|"); '(l, Ident cn); '(_, Kwd "("); ts = parse_types; cs = parse_ctors >] -> Ctor (l, cn, ts)::cs
| [< >] -> []
and
  parse_types = parser
  [< '(_, Kwd ")") >] -> []
| [< t = parse_type; ts = parse_more_types >] -> t::ts
and
  parse_more_types = parser
  [< '(_, Kwd ","); t = parse_type; ts = parse_more_types >] -> t::ts
| [< '(_, Kwd ")") >] -> []
and
  parse_fields = parser
  [< '(_, Kwd "}") >] -> []
| [< f = parse_field; fs = parse_fields >] -> f::fs
and
  parse_field = parser
  [< t = parse_type; '(l, Ident f); '(_, Kwd ";") >] -> Field (l, t, f)
and
  parse_func_kind = parser
  [< '(_, Kwd "fixpoint") >] -> Fixpoint
| [< '(_, Kwd "lemma") >] -> Lemma
| [< >] -> Regular
and
  parse_return_type = parser
  [< '(_, Kwd "void") >] -> None
| [< t = parse_type >] -> Some t
and
  parse_type = parser
  [< (l, tn) = parse_primary_type; tt = parse_type_suffix l tn >] -> tt
and
  parse_primary_type = parser
  [< '(l, Kwd "struct"); '(_, Ident s) >] -> (l, s)
| [< '(l, Ident n) >] -> (l, n)
and
  parse_type_suffix tnl tn = parser
  [< '(l, Kwd "*") >] -> PtrType (l, tn)
| [< >] -> TypeName (tnl, tn)
and
  parse_paramlist = parser
  [< '(_, Kwd ")") >] -> []
| [< p = parse_param; ps = parse_more_params >] -> p::ps
and
  parse_param = parser
  [< t = parse_type; '(l, Ident pn) >] -> (t, pn)
and
  parse_more_params = parser
  [< '(_, Kwd ","); p = parse_param; ps = parse_more_params >] -> p::ps
| [< '(_, Kwd ")") >] -> []
and
  parse_contract_opt = parser
  [< '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "ensures"); q = parse_pred; '(_, Kwd ";") >] -> Some (p, q)
| [< >] -> None
and
  parse_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> ss
and
  parse_stmts = parser
  [< s = parse_stmt; ss = parse_stmts >] -> s::ss
| [< >] -> []
and
  parse_stmt = parser
  [< '(l, Kwd "if"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); b1 = parse_block; '(_, Kwd "else"); b2 = parse_block >] -> IfStmt (l, e, b1, b2)
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); sscs = parse_switch_stmt_clauses; '(_, Kwd "}"); '(_, Kwd "}") >] -> SwitchStmt (l, e, sscs)
| [< '(l, Kwd "open"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Open (l, g, es) | _ -> raise (Stream.Error "Body of open statement must be call expression."))
| [< '(l, Kwd "close"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Close (l, g, es) | _ -> raise (Stream.Error "Body of close statement must be call expression."))
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "invariant"); p = parse_pred; b = parse_block >] -> WhileStmt (l, e, p, b)
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] -> (match e with CallExpr (l, g, es) -> CallStmt (l, g, es) | _ -> raise (Stream.Error "An expression used as a statement must be a call expression."))
  | [< '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] ->
    (match e with
     | Var (_, x) -> Assign (l, x, rhs)
     | Read (_, e, f) -> Write (l, e, f, rhs)
     | _ -> raise (Stream.Error "The left-hand side of an assignment must be an identifier or a field dereference expression.")
    )
  | [< '(_, Ident x); '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] ->
    (match e with
     | TypeExpr (_, t) -> DeclStmt (l, t, x, rhs)
     | _ -> raise (Stream.Error "A local variable declaration statement must start with a type expression.")
    )
  >] -> s
and
  parse_switch_stmt_clauses = parser
  [< c = parse_switch_stmt_clause; cs = parse_switch_stmt_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_stmt_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(_, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); ss = parse_stmts >] -> SwitchStmtClause (l, c, pats, ss)
and
  parse_more_pats = parser
  [< '(_, Kwd ")") >] -> []
| [< '(_, Kwd ","); '(_, Ident x); xs = parse_more_pats >] -> x::xs
and
  parse_pred = parser
  [< p0 = parse_pred0; p = parse_sep_rest p0 >] -> p
and
  parse_sep_rest p1 = parser
  [< '(l, Kwd "&*&"); p2 = parse_pred0; p = parse_sep_rest (Sep (l, p1, p2)) >] -> p
| [< >] -> p1
and
  parse_pred0 = parser
  [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_pred_clauses; '(_, Kwd "}") >] -> SwitchPred (l, e, cs)
| [< '(l, Kwd "emp") >] -> EmpPred l
| [< e = parse_conj_expr; p = parser
    [< '(l, Kwd "|->"); rhs = parse_expr >] ->
    (match e with
     | Read (_, e, f) -> Access (l, e, f, rhs)
     | _ -> raise (Stream.Error "Left-hand side of access predicate must be a field dereference expression.")
    )
  | [< '(l, Kwd "?"); p1 = parse_pred; '(_, Kwd ":"); p2 = parse_pred >] -> IfPred (l, e, p1, p2)
  | [< >] ->
    (match e with
     | CallExpr (l, g, es) -> CallPred (l, g, es)
     | _ -> ExprPred (expr_loc e, e)
    )
  >] -> p
and
  parse_switch_pred_clauses = parser
  [< c = parse_switch_pred_clause; cs = parse_switch_pred_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_pred_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(_, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); p = parse_pred; '(_, Kwd ";") >] -> SwitchPredClause (l, c, pats, p)
and
  parse_expr = parser
  [< e0 = parse_conj_expr; e = parser
    [< '(l, Kwd "?"); e1 = parse_expr; '(_, Kwd ":"); e2 = parse_expr >] -> IfExpr (l, e0, e1, e2)
  | [< >] -> e0
  >] -> e
and
  parse_conj_expr = parser
  [< e0 = parse_expr_rel; e = parse_expr_conj_rest e0 >] -> e
and
  parse_expr_rel = parser
  [< e0 = parse_expr_arith; e = parse_expr_rel_rest e0 >] -> e
and
  parse_expr_arith = parser
  [< e0 = parse_expr_suffix; e = parse_expr_arith_rest e0 >] -> e
and
  parse_expr_suffix = parser
  [< e0 = parse_expr_primary; e = parse_expr_suffix_rest e0 >] -> e
and
  parse_expr_primary = parser
  [< '(l, Ident x); e = parser [< args = parse_arglist >] -> CallExpr (l, x, args) | [< >] -> Var (l, x) >] -> e
| [< '(l, Int i) >] -> Operation (l, string_of_int i, [])
| [< '(l, Kwd "true") >] -> Operation (l, "true", [])
| [< '(l, Kwd "("); e = parse_expr; '(_, Kwd ")") >] -> e
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses; '(_, Kwd "}") >] -> SwitchExpr (l, e, cs)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "struct"); '(_, Ident s); t = parse_type_suffix l s >] -> TypeExpr (type_loc t, t)
and
  parse_switch_expr_clauses = parser
  [< c = parse_switch_expr_clause; cs = parse_switch_expr_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_expr_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(_, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> SwitchExprClause (l, c, pats, e)
and
  parse_expr_suffix_rest e0 = parser
  [< '(l, Kwd "->"); '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, f)) >] -> e
| [< >] -> e0
and
  parse_expr_arith_rest e0 = parser
  [< '(l, Kwd "+"); e1 = parse_expr_suffix; e = parse_expr_arith_rest (Operation (l, "+", [e0; e1])) >] -> e
| [< '(l, Kwd "-"); e1 = parse_expr_suffix; e = parse_expr_arith_rest (Operation (l, "-", [e0; e1])) >] -> e
| [< >] -> e0
and
  parse_expr_rel_rest e0 = parser
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "EQ", [e0; e1])) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "NEQ", [e0; e1])) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "<=", [e0; e1])) >] -> e
| [< '(l, Kwd "<"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "<", [e0; e1])) >] -> e
| [< >] -> e0
and
  parse_expr_conj_rest e0 = parser
  [< '(l, Kwd "&&"); e1 = parse_expr_rel; e = parse_expr_conj_rest (Operation (l, "AND", [e0; e1])) >] -> e
| [< >] -> e0
and
  parse_arglist = parser
  [< '(l, Kwd "("); es = parser [< '(_, Kwd ")") >] -> [] | [< e0 = parse_expr; es = parse_arglist_rest >] -> e0::es >] -> es
and
  parse_arglist_rest = parser
  [< '(_, Kwd ","); e0 = parse_expr; es = parse_arglist_rest >] -> e0::es
| [< '(_, Kwd ")") >] -> []
in
  try
    try
      let p = parse_program token_stream in close_in c; p
    with Stream.Error msg -> let (line, column) = loc() in raise (Stream.Error (msg ^ " at (" ^ string_of_int line ^ ":" ^ string_of_int column ^ ")"))
  with ex -> close_in c; raise ex

let _ = read_program "linkedlist.c"

end
