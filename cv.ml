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
  | CallExpr of loc * string * pat list
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of loc * expr * switch_expr_clause list
  | SizeofExpr of loc * type_expr
  | TypeExpr of loc * type_expr
and
  pat =
    LitPat of expr
  | VarPat of string
  | DummyPat
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
  | Open of loc * string * pat list
  | Close of loc * string * pat list
  | ReturnStmt of loc * expr option
  | WhileStmt of loc * expr * pred * stmt list
and
  switch_stmt_clause =
  | SwitchStmtClause of loc * string * string list * stmt list
and
  pred =
    Access of loc * expr * string * pat
  | CallPred of loc * string * pat list
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
  | CallExpr (l, g, pats) -> l
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
  
let stmt_loc s =
  match s with
    Assign (l, _, _) -> l
  | DeclStmt (l, _, _, _) -> l
  | Write (l, _, _, _) -> l
  | CallStmt (l,  _, _) -> l
  | IfStmt (l, _, _, _) -> l
  | SwitchStmt (l, _, _) -> l
  | Open (l, _, _) -> l
  | Close (l, _, _) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _) -> l

let type_loc t =
  match t with
    TypeName (l, n) -> l
  | PtrType (l, n) -> l

let lexer = make_lexer [
  "struct"; "{"; "}"; "*"; ";"; "int"; "predicate"; "("; ")"; ","; "requires";
  "->"; "|->"; "&*&"; "inductive"; "="; "|"; "fixpoint"; "switch"; "case"; ":";
  "return"; "+"; "-"; "=="; "?"; "true"; "ensures"; "sizeof"; "close"; "void"; "lemma";
  "open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; "<="; "&&"; "forall"; "_"
]

let read_program s =
  let c = open_in s in
  let (loc, token_stream) = lexer (Stream.of_channel c) in
let rec parse_program = parser
  [< ds = parse_decls; _ = Stream.empty >] -> Program ds
and
  parse_decls = parser
  [< d = parse_decl; ds = parse_decls >] -> d::ds
| [< >] -> []
and
  parse_decl = parser
  [< '(l, Kwd "inductive"); '(_, Ident i); '(_, Kwd "="); cs = parse_ctors; '(_, Kwd ";") >] -> Inductive (l, i, cs)
| [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, fs)
  | [< t = parse_type_suffix l s; d = parse_func_rest Regular (Some t) >] -> d
  >] -> d
| [< '(l, Kwd "predicate"); '(_, Ident g); '(_, Kwd "("); ps = parse_paramlist; '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); >] -> PredDecl (l, g, ps, p)
| [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> d
| [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest Lemma t >] -> d
| [< t = parse_return_type; d = parse_func_rest Regular t >] -> d
and
  parse_func_rest k t = parser
  [< '(l, Ident g); '(_, Kwd "("); ps = parse_paramlist; co = parse_contract_opt; ss = parse_block >] -> Func (l, k, t, g, ps, co, ss)
and
  parse_ctors = parser
  [< '(_, Kwd "|"); '(l, Ident cn); ts = (parser [< '(_, Kwd "("); ts = parse_types >] -> ts | [< >] -> []); cs = parse_ctors >] -> Ctor (l, cn, ts)::cs
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
  parse_return_type = parser
  [< '(_, Kwd "void") >] -> None
| [< t = parse_type >] -> Some t
and
  parse_type = parser
  [< (l, tn) = parse_primary_type; tt = parse_type_suffix l tn >] -> tt
and
  parse_primary_type = parser
  [< '(l, Kwd "struct"); '(_, Ident s) >] -> (l, s)
| [< '(l, Kwd "int") >] -> (l, "int")
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
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); sscs = parse_switch_stmt_clauses; '(_, Kwd "}") >] -> SwitchStmt (l, e, sscs)
| [< '(l, Kwd "open"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Open (l, g, es) | _ -> raise (Stream.Error "Body of open statement must be call expression."))
| [< '(l, Kwd "close"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Close (l, g, es) | _ -> raise (Stream.Error "Body of close statement must be call expression."))
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); b = parse_block >] -> WhileStmt (l, e, p, b)
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] -> (match e with CallExpr (l, g, es) -> CallStmt (l, g, List.map (function LitPat e -> e) es) | _ -> raise (Stream.Error "An expression used as a statement must be a call expression."))
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
    [< '(l, Kwd "|->"); rhs = parse_pattern >] ->
    (match e with
     | Read (_, e, f) -> Access (l, e, f, rhs)
     | _ -> raise (Stream.Error "Left-hand side of access predicate must be a field dereference expression.")
    )
  | [< '(l, Kwd "?"); p1 = parse_pred; '(_, Kwd ":"); p2 = parse_pred >] -> IfPred (l, e, p1, p2)
  | [< >] ->
    (match e with
     | CallExpr (l, g, pats) -> CallPred (l, g, pats)
     | _ -> ExprPred (expr_loc e, e)
    )
  >] -> p
and
  parse_pattern = parser
  [< '(_, Kwd "_") >] -> DummyPat
| [< '(_, Kwd "?"); '(_, Ident x) >] -> VarPat x
| [< e = parse_expr >] -> LitPat e
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
  [< '(l, Ident x); e = parser [< args = parse_patlist >] -> CallExpr (l, x, args) | [< >] -> Var (l, x) >] -> e
| [< '(l, Int i) >] -> Operation (l, string_of_int i, [])
| [< '(l, Kwd "true") >] -> Operation (l, "true", [])
| [< '(l, Kwd "("); e = parse_expr; '(_, Kwd ")") >] -> e
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses; '(_, Kwd "}") >] -> SwitchExpr (l, e, cs)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "struct"); '(_, Ident s); t = parse_type_suffix l s >] -> TypeExpr (type_loc t, t)
| [< '(l, Kwd "int") >] -> TypeExpr (l, TypeName (l, "int"))
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
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "==", [e0; e1])) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "!=", [e0; e1])) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "le", [e0; e1])) >] -> e
| [< '(l, Kwd "<"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, "lt", [e0; e1])) >] -> e
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
and
  parse_patlist = parser
  [< '(l, Kwd "("); pats = parser [< '(_, Kwd ")") >] -> [] | [< pat0 = parse_pattern; pats = parse_patlist_rest >] -> pat0::pats >] -> pats
and
  parse_patlist_rest = parser
  [< '(_, Kwd ","); pat0 = parse_pattern; pats = parse_patlist_rest >] -> pat0::pats
| [< '(_, Kwd ")") >] -> []
in
  try
    try
      let p = parse_program token_stream in close_in c; p
    with Stream.Error msg -> let (line, column) = loc() in raise (Stream.Error (msg ^ " at (" ^ string_of_int line ^ ":" ^ string_of_int column ^ ")"))
  with ex -> close_in c; raise ex

let flatmap f xs = List.concat (List.map f xs)

let theory = [
  "(DISTINCT true false)";
  "(FORALL (e1 e2) (EQ (IF true e1 e2) e1))";
  "(FORALL (e1 e2) (EQ (IF false e1 e2) e2))";
  "(FORALL (e1 e2) (IFF (EQ (== e1 e2) true) (EQ e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (!= e1 e2) true) (NEQ e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (le e1 e2) true) (<= e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (lt e1 e2) true) (< e1 e2)))"
]

type
  term =
    Int of int
  | Symb of string
  | FunApp of string * term list
  | IfTerm of term * term * term
and
  formula =
    True
  | PredApp of string * term list
  | Eq of term * term
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | IfFormula of formula * formula * formula
  | Forall of string list * formula

let slist ss =
  let rec args ss =
    match ss with
      [] -> ""
    | [s] -> s
    | (s::ss) -> s ^ " " ^ args ss
  in
    "(" ^ args ss ^ ")"

let rec simpt t =
  match t with
    Int i -> string_of_int i
  | Symb s -> s
  | FunApp (f, ts) -> slist ([f] @ List.map simpt ts)
  | IfTerm (t1, t2, t3) -> slist ["IF"; simpt t1; simpt t2; simpt t3]

let rec simp f =
  match f with
    True -> "TRUE"
  | PredApp (p, ts) -> slist (p :: List.map simpt ts)
  | Eq (t1, t2) -> "(EQ " ^ simpt t1 ^ " " ^ simpt t2 ^ ")"
  | Not f -> "(NOT " ^ simp f ^ ")"
  | And (f1, f2) -> "(AND " ^ simp f1 ^ " " ^ simp f2 ^ ")"
  | Or (f1, f2) -> "(OR " ^ simp f1 ^ " " ^ simp f2 ^ ")"
  | Imp (f1, f2) -> slist ["IMPLIES"; simp f1; simp f2]
  | Iff (f1, f2) -> slist ["IFF"; simp f1; simp f2]
  | IfFormula (f1, f2, f3) -> let s1 = simp f1 in slist ["AND"; slist ["IMPLIES"; s1; simp f2]; slist ["IMPLIES"; slist ["NOT"; s1]; simp f3]]
  | Forall (xs, f) -> slist ["FORALL"; slist xs; simp f]

let rec conj ts : formula =
  match ts with
    [] -> True
  | t :: ts -> And (t, conj ts)

let lookup env x = if List.mem_assoc x env then List.assoc x env else Symb x
let update env x t = (x, t)::env
let string_of_env env = slist (List.map (function (x, t) -> slist [x; simpt t]) env)

let rec eval env e =
  let ev = eval env in
  match e with
    Var (l, x) -> lookup env x
  | Operation (l, op, es) -> (match es with [] -> Symb op | _ -> FunApp (op, List.map ev es))
(*  | Read (l, e, f) ->  *)
  | CallExpr (l, g, pats) -> FunApp (g, List.map (function (LitPat e) -> ev e) pats)
  | IfExpr (l, e1, e2, e3) -> IfTerm (ev e1, ev e2, ev e3)
(*  | SwitchExpr (l, e, cs) *)
  | SizeofExpr (l, t) ->
    match t with
      TypeName (_, tn) -> Symb ("sizeof_" ^ tn)
    | PtrType (_, tn) -> Symb "sizeof_ptr"

let rec exptrue env e =
  let etrue = exptrue env in
  let ev = eval env in
  match e with
    Operation (_, "==", [e1; e2]) -> Eq (ev e1, ev e2)
  | Operation (_, "!=", [e1; e2]) -> Not (Eq (ev e1, ev e2))
  | Operation (_, "le", [e1; e2]) -> PredApp ("<=", [ev e1; ev e2])
  | Operation (_, "lt", [e1; e2]) -> PredApp ("<", [ev e1; ev e2])
  | Operation (_, "&&", [e1; e2]) -> And (etrue e1, etrue e2)
  | _ -> Eq (ev e, Symb "true")

let zip xs ys =
  let rec iter xs ys zs =
    match (xs, ys) with
      ([], []) -> Some (List.rev zs)
    | (x::xs, y::ys) -> iter xs ys ((x, y)::zs)
    | _ -> None
  in
  iter xs ys []
  
let verify_program path =

  let verbose = ref true in

  let verbose_print_endline s = if !verbose then print_endline s else () in
  let verbose_print_string s = if !verbose then print_string s else () in

  let unique_number_counter = ref 0 in

  let get_unique_number () =
    let n = !unique_number_counter in
    unique_number_counter := n + 1;
    n
  in

  let get_unique_id s =
    s ^ string_of_int (get_unique_number ())
  in
  
  let get_unique_symb s = Symb (get_unique_id s) in

  let Program ds = read_program "linkedlist.c" in
  
  let (simp_in, simp_out) = Unix.open_process "z3 /si" in
  
  let imap f xs =
    let rec imapi i xs =
      match xs with
        [] -> []
      | x::xs -> f i x::imapi (i + 1) xs
    in
    imapi 0 xs
  in
  
  let indaxs =
    flatmap
    (function
       Inductive (l, i, cs) ->
       let tags = List.map (function (Ctor (l, c, ps)) -> "ctortag_" ^ c) cs in
       let da = slist ("DISTINCT" :: tags) in
       let tagaxs =
         List.map
           (function (Ctor (l, c, ps)) ->
              match ps with
                [] -> slist ["EQ"; slist ["tagfunc_" ^ i; c]; "ctortag_" ^ c]
              | _ ->
                let xs = imap (fun i t -> "x" ^ string_of_int i) ps in
                slist ["FORALL"; slist xs; slist ["PATS"; slist (c :: xs)]; slist ["EQ"; slist ["tagfunc_" ^ i; slist (c :: xs)]; "ctortag_" ^ c]]
           )
           cs
       in
       let projaxs =
         flatmap
           (function (Ctor (l, c, ps)) ->
              let xs = imap (fun i t -> "x" ^ string_of_int i) ps in
              List.map
                (fun x ->
                   slist ["FORALL"; slist xs; slist ["PATS"; slist (c :: xs)]; slist ["EQ"; slist ["projfunc_" ^ c ^ "_" ^ x; slist (c :: xs)]; x]]
                )
                xs
           )
           cs
       in
       da :: tagaxs @ projaxs
     | Func (l, Fixpoint, t, g, ps, _, [SwitchStmt (_, Var (_, x), cs)]) ->
       let xs = List.map (fun (t, x) -> x) ps in
       List.map
         (function (SwitchStmtClause (lc, cn, pats, [ReturnStmt (_, Some e)])) ->
            let xs' = flatmap (fun y -> if y = x then pats else [y]) xs in
            let args = List.map (fun y -> if y = x then match pats with [] -> cn | _ -> slist (cn :: pats) else y) xs in
            let env = List.map (fun x -> (x, Symb x)) xs' in
            let body = slist ["EQ"; slist (g :: args); simpt (eval env e)] in
            match xs' with
              [] -> body
            | _ -> slist ["FORALL"; slist xs'; slist ["PATS"; slist (g :: args)]; body]
         )
         cs
     | _ -> []
    )
    ds
  in

  let send_command c =
    verbose_print_endline c;
    output_string simp_out c;
    output_string simp_out "\r\n";
    flush simp_out
  in

  let bg_push s = send_command (slist ["BG_PUSH"; s]) in

  let _ = bg_push (slist ("AND" :: theory)) in
  
  let _ = bg_push (slist ("AND" :: List.map (fun s -> s ^ "\r\n") indaxs)) in

  let getch() = input_char simp_in in
  
  let getline() = input_line simp_in in
  
  let rec input_reply() =
    let line = getline() in
    let line = String.sub line 0 (String.length line - 1) in
    [line] @ (if String.length line > 0 && String.get line (String.length line - 1) = '.' then [] else input_reply())
  in
  
  let query_count = ref 0 in
  
  let query_formula phi =
    send_command (simp phi);
    let reply = input_reply() in
    List.iter verbose_print_endline reply;
    let success = (reply = [string_of_int !query_count ^ ": Valid."]) in
    query_count := !query_count + 1;
    success
  in
  
  let assume phi cont =
    bg_push (simp phi);
    cont();
    send_command "(BG_POP)"
  in
  
  let assert_formula phi l msg cont =
    (if not (query_formula phi) then failwith (string_of_loc l ^ msg));
    cont()
  in
  
  let success() = () in
  
  let branch cont1 cont2 =
    cont1();
    cont2()
  in
  
  let evalpat env pat cont =
    match pat with
      LitPat e -> cont env (eval env e)
    | VarPat x -> let t = get_unique_symb x in cont (update env x t) t
    | DummyPat -> let t = get_unique_symb "dummy" in cont env t
  in
  
  let rec evalpats env pats cont =
    match pats with
      [] -> cont env []
    | pat::pats -> evalpat env pat (fun env t -> evalpats env pats (fun env ts -> cont env (t::ts)))
  in
  
  let assume_field h0 f tp tv cont =
    let rec iter h =
      match h with
        [] -> cont (("field_" ^ f, [tp; tv])::h0)
      | (g, [tp'; _])::h when g = "field_" ^ f -> assume (Not (Eq (tp, tp'))) (fun _ -> iter h)
      | _::h -> iter h
    in
    iter h0
  in
  
  let rec assume_pred h env p cont =
    let ev = eval env in
    let etrue = exptrue env in
    match p with
    | Access (l, e, f, rhs) -> let te = ev e in evalpat env rhs (fun env t -> assume_field h f te t (fun h -> cont h env))
    | CallPred (l, g, pats) -> evalpats env pats (fun env ts -> cont ((g, ts)::h) env)
    | ExprPred (l, e) -> assume (etrue e) (fun _ -> cont h env)
    | Sep (l, p1, p2) -> assume_pred h env p1 (fun h env -> assume_pred h env p2 cont)
    | IfPred (l, e, p1, p2) -> branch (fun _ -> assume (etrue e) (fun _ -> assume_pred h env p1 cont)) (fun _ -> assume (Not (etrue e)) (fun _ -> assume_pred h env p2 cont))
    | SwitchPred (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          branch
            (fun _ ->
               let xts = List.map (fun x -> (x, get_unique_symb x)) pats in
               assume (Eq (t, FunApp(cn, List.map (fun (x, t) -> t) xts))) (fun _ -> assume_pred h (xts @ env) p cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h env
  in
  
  let definitely_equal t1 t2 =
    if t1 = t2 then true else query_formula (Eq (t1, t2))
  in
  
  let match_chunk env g pats (g', ts0) =
    let rec iter env pats ts =
      match (pats, ts) with
        (LitPat e::pats, t::ts) -> if definitely_equal (eval env e) t then iter env pats ts else None
      | (VarPat x::pats, t::ts) -> iter (update env x t) pats ts
      | (DummyPat::pats, t::ts) -> iter env pats ts
      | ([], []) -> Some (ts0, env)
    in
      if g = g' then
        iter env pats ts0
      else
        None
  in
  
  let assert_chunk h env l g pats cont =
    let rec iter hprefix h =
      match h with
        [] -> []
      | chunk::h ->
        let matches =
          match match_chunk env g pats chunk with
            None -> []
          | Some (ts, env) -> [(hprefix @ h, ts, env)]
        in
          matches @ iter (chunk::hprefix) h
    in
    match iter [] h with
      [] -> assert_formula (Not True) l "No matching heap chunks." (fun _ -> success())
    | [(h, ts, env)] -> cont h ts env
    | _ -> assert_formula (Not True) l "Multiple matching heap chunks." (fun _ -> success())
  in
  
  let rec assert_pred h env p cont =
    let ev = eval env in
    let etrue = exptrue env in
    match p with
    | Access (l, e, f, rhs) ->
      assert_chunk h env l ("field_" ^ f) [LitPat e; rhs] (fun h ts env -> cont h env)
    | CallPred (l, g, pats) ->
      assert_chunk h env l g pats (fun h ts env -> cont h env)
    | ExprPred (l, e) ->
      assert_formula (etrue e) l "Expression is false." (fun _ -> cont h env)
    | Sep (l, p1, p2) ->
      assert_pred h env p1 (fun h env -> assert_pred h env p2 cont)
    | IfPred (l, e, p1, p2) ->
      branch
        (fun _ ->
           assume (etrue e) (fun _ ->
             assert_pred h env p1 cont))
        (fun _ ->
           assume (Not (etrue e)) (fun _ ->
             assert_pred h env p2 cont))
    | SwitchPred (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          let xts = List.map (fun x -> (x, get_unique_symb x)) pats in
          branch
            (fun _ -> assume (Eq (t, FunApp (cn, List.map (fun (x, t) -> t) xts))) (fun _ -> assert_pred h (xts @ env) p cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h env
  in

  let rec block_assigned_variables ss =
    match ss with
      [] -> []
    | s::ss -> assigned_variables s @ block_assigned_variables ss
  and assigned_variables s =
    match s with
      Assign (l, x, e) -> [x]
    | IfStmt (l, e, ss1, ss2) -> block_assigned_variables ss1 @ block_assigned_variables ss2
    | SwitchStmt (l, e, cs) -> failwith (string_of_loc l ^ ": Switch statements inside loops are not supported.")
    | WhileStmt (l, e, p, ss) -> block_assigned_variables ss
    | _ -> []
  in
  
  let get_field h t f l cont =
    assert_chunk h [("x", t)] l ("field_" ^ f) [LitPat (Var ((0, 0), "x")); VarPat "y"] (fun h ts env ->
      cont h (lookup env "y"))
  in

  let rec verify_stmt tenv h env s tcont =
    let (line, col) = stmt_loc s in
    let _ = print_endline (path ^ ":" ^ string_of_int line ^ ":" ^ string_of_int col ^ ": Checking statement...") in
    let _ = print_endline ("Heap: " ^ slist (List.map (function (g, ts) -> slist (g::List.map simpt ts)) h)) in
    let _ = print_endline ("Env: " ^ string_of_env env) in
    let ev = eval env in
    let etrue = exptrue env in
    let cont = tcont tenv in
    match s with
      Assign (l, x, Read (lr, e, f)) ->
      let t = ev e in
      get_field h t f l (fun _ v ->
        cont h (update env x v))
    | Assign (l, x, CallExpr (lc, "assert", [LitPat e])) ->
      assert_formula (etrue e) l "Assertion failure." (fun _ -> cont h env)
    | Assign (l, x, CallExpr (lc, "malloc", [LitPat (SizeofExpr (lsoe, TypeName (ltn, tn)))])) ->
      let [fds] = flatmap (function (Struct (ls, sn, fds)) when sn = tn -> [fds] | _ -> []) ds in
      let result = get_unique_symb "block" in
      let rec iter h fds =
        match fds with
          [] -> cont (h @ [("malloc_block_" ^ tn, [result])]) (update env x result)
        | Field (lf, t, f)::fds -> assume_field h f result (get_unique_symb "value") (fun h -> iter h fds)
      in
      iter h fds
    | CallStmt (l, "free", [Var (lv, x)]) ->
      let (PtrType (_, tn)) = tenv x in
      let [fds] = flatmap (function (Struct (ls, sn, fds)) when sn = tn -> [fds] | _ -> []) ds in
      let rec iter h fds =
        match fds with
          [] -> cont h env
        | (Field (lf, t, f))::fds -> get_field h (lookup env x) f l (fun h _ -> iter h fds)
      in
      assert_chunk h env l ("malloc_block_" ^ tn) [LitPat (Var (lv, x))] (fun h _ _ -> iter h fds)
    | Assign (l, x, CallExpr (lc, g, pats)) ->
      let ts = List.map (function (LitPat e) -> ev e) pats in
      let fds = flatmap (function (Func (lg, k, tr, g', ps, Some (pre, post), _)) when g = g' && k != Fixpoint -> [(ps, pre, post)] | _ -> []) ds in
      (
      match fds with
        [] -> cont h (update env x (FunApp (g, ts)))
      | [(ps, pre, post)] ->
        let ys = List.map (function (t, p) -> p) ps in
        let Some env' = zip ys ts in
        assert_pred h env' pre (fun h env' ->
          let r = get_unique_symb "result" in
          let env'' = update env' "result" r in
          assume_pred h env'' post (fun h _ ->
            cont h (update env x r))
        )
      )
    | Assign (l, x, e) ->
      cont h (update env x (ev e))
    | DeclStmt (l, t, x, e) ->
      verify_stmt (fun y -> if y = x then t else tenv y) h env (Assign (l, x, e)) tcont
    | Write (l, e, f, rhs) ->
      let t = ev e in
      get_field h t f l (fun h _ ->
        cont (("field_" ^ f, [t; ev rhs])::h) env)
    | CallStmt (l, g, es) ->
      let x = get_unique_id "|<result>|" in   (* HACK *)
      verify_stmt tenv h env (Assign (l, x, CallExpr (l, g, List.map (fun e -> LitPat e) es))) tcont
    | IfStmt (l, e, ss1, ss2) ->
      let t = ev e in
      branch
        (fun _ -> assume (Eq (t, Symb "true")) (fun _ -> verify_cont tenv h env ss1 tcont))
        (fun _ -> assume (Eq (t, Symb "false")) (fun _ -> verify_cont tenv h env ss2 tcont))
    | SwitchStmt (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          [] -> success()
        | SwitchStmtClause (lc, cn, pats, ss)::cs ->
          let xts = List.map (fun x -> (x, get_unique_symb x)) pats in
          branch
            (fun _ -> assume (Eq (t, FunApp (cn, List.map (fun (x, t) -> t) xts))) (fun _ -> verify_cont tenv h (xts @ env) ss tcont))
            (fun _ -> iter cs)
      in
      iter cs
    | Open (l, g, pats) ->
      assert_chunk h env l g pats (fun h ts env ->
        let [(lpd, ps, p)] = flatmap (function PredDecl (lpd, g', ps, p) when g = g' -> [(lpd, ps, p)] | _ -> []) ds in
        let ys = List.map (function (t, p) -> p) ps in
        let Some env' = zip ys ts in
        assume_pred h env' p (fun h _ ->
          cont h env))
    | Close (l, g, pats) ->
      let ts = List.map (function LitPat e -> ev e) pats in
      let [(lpd, ps, p)] = flatmap (function PredDecl (lpd, g', ps, p) when g = g' -> [(lpd, ps, p)] | _ -> []) ds in
      let ys = List.map (function (t, p) -> p) ps in
      let Some env' = zip ys ts in
      assert_pred h env' p (fun h _ ->
        cont ((g, ts)::h) env)
    | ReturnStmt (l, Some e) ->
      cont h (update env "result" (ev e))
    | ReturnStmt (l, None) -> cont h env
    | WhileStmt (l, e, p, ss) ->
      let xs = block_assigned_variables ss in
      assert_pred h env p (fun h env ->
        let ts = List.map get_unique_symb xs in
        let Some bs = zip xs ts in
        let env = bs @ env in
        branch
          (fun _ ->
             assume_pred [] env p (fun h env ->
               assume (exptrue env e) (fun _ ->
                 verify_cont tenv h env ss (fun tenv h env ->
                   assert_pred h env p (fun h _ ->
                     match h with
                       [] -> success()
                     | _ -> assert_formula (Not True) l "Loop leaks heap chunks." (fun _ -> success())
                   )
                 )
               )
             )
          )
          (fun _ ->
             assume_pred h env p (fun h env ->
               assume (Not (exptrue env e)) (fun _ ->
                 cont h env)))
      )
  and
    verify_cont tenv h env ss cont =
    match ss with
      [] -> cont tenv h env
    | s::ss -> verify_stmt tenv h env s (fun tenv h env -> verify_cont tenv h env ss cont)
  in
  
  let verify_decl d =
    match d with
      Func (l, Fixpoint, _, _, _, _, _) -> ()
    | Func (l, _, _, g, ps, Some (pre, post), ss) ->
      let env = List.map (function (t, p) -> (p, Symb p)) ps in
      let pts = List.map (function (t, p) -> (p, t)) ps in
      let tenv x = List.assoc x pts in
      assume_pred [] env pre (fun h env ->
        verify_cont tenv h env ss (fun _ h env' ->
          assert_pred h (update env "result" (lookup env' "result")) post (fun h _ ->
            match h with
              [] -> success()
            | _ -> assert_formula (Not True) l "Function leaks heap chunks." (fun _ -> success())
          )
        )
      )
    | _ -> ()
  in
  
  List.iter verify_decl ds;
  print_endline "0 errors found"

let _ = verify_program "linkedlist.c"

end
