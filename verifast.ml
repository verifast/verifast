module CVerifier =
struct

type token =
    Kwd of string
  | Ident of string
  | Int of int
  | Float of float
  | String of string
  | Char of char

(* The lexer *)

let make_lexer keywords path =
  let channel = open_in path in
  let stream = Stream.of_channel channel in
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

  let in_single_line_annotation = ref false in
  
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
    let new_line strm__ =
      line := !line + 1;
      linepos := Stream.count strm__;
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        Some (Kwd "@*/")
      ) else
        next_token strm__
    in
    match Stream.peek strm__ with
      Some (' ' | '\009' | '\026' | '\012') ->
        Stream.junk strm__; next_token strm__
    | Some '\010' ->
        Stream.junk strm__; new_line strm__
    | Some '\013' ->
        Stream.junk strm__;
        if Stream.peek strm__ = Some '\010' then Stream.junk strm__;
        new_line strm__
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
      Stream.junk strm__;
      (
        match Stream.peek strm__ with
          Some '@' -> (Stream.junk strm__; in_single_line_annotation := true; Some (Kwd "/*@"))
        | _ ->
          if !in_single_line_annotation then (
            in_single_line_annotation := false; single_line_comment strm__; Some (Kwd "@*/")
          ) else (
            single_line_comment strm__; next_token strm__
          )
      )
    | Some '*' ->
      Stream.junk strm__;
      (
        match Stream.peek strm__ with
          Some '@' -> (Stream.junk strm__; Some (Kwd "/*@"))
        | _ -> (multiline_comment strm__; next_token strm__)
      )
    | _ -> Some (keyword_or_error '/')
  and single_line_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\010' | Some '\013' -> ()
    | Some c -> Stream.junk strm__; single_line_comment strm__
    | _ -> raise Stream.Failure
  and multiline_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '*' ->
      (
        Stream.junk strm__;
        (
          match Stream.peek strm__ with
            Some '/' -> (Stream.junk strm__; ())
          | _ -> multiline_comment strm__
        )
      )
    | _ -> (Stream.junk strm__; multiline_comment strm__)
  in
  (channel, (fun () -> (path, !line, Stream.count stream - !linepos + 1)), Stream.from (fun count -> (match next_token stream with Some t -> Some ((path, !line, !tokenpos - !linepos + 1), t) | None -> None)))

type
  operator = string
and
 loc = (string * int * int)
and
  expr =
    Var of loc * string
  | Operation of loc * operator * expr list
  | IntLit of loc * int
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
    PureStmt of loc * stmt
  | Assign of loc * string * expr
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

(*
Visual Studio format:
C:\ddd\sss.xyz(123): error VF0001: blah
C:\ddd\sss.xyz(123,456): error VF0001: blah
C:\ddd\sss.xyz(123,456-789): error VF0001: blah
C:\ddd\sss.xyz(123,456-789,123): error VF0001: blah
GNU format:
C:\ddd\sss.xyz:123: error VF0001: blah
C:\ddd\sss.xyz:123.456: error VF0001: blah
C:\ddd\sss.xyz:123.456-789: error VF0001: blah
C:\ddd\sss.xyz:123.456-789.123: error VF0001: blah
See
http://blogs.msdn.com/msbuild/archive/2006/11/03/msbuild-visual-studio-aware-error-messages-and-message-formats.aspx
and
http://www.gnu.org/prep/standards/standards.html#Errors
*)

let string_of_loc (p,l,c) = p ^ "(" ^ string_of_int l ^ "," ^ string_of_int c ^ ")"

let expr_loc e =
  match e with
    Var (l, x) -> l
  | IntLit (l, n) -> l
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
    PureStmt (l, _) -> l
  | Assign (l, _, _) -> l
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
  "return"; "+"; "-"; "=="; "?"; "ensures"; "sizeof"; "close"; "void"; "lemma";
  "open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; "<="; "&&"; "forall"; "_"; "@*/"
]

let read_program s =
  let (c, loc, token_stream) = lexer s in
let rec parse_program = parser
  [< ds = parse_decls; _ = Stream.empty >] -> Program ds
and
  parse_decls = parser
  [< d = parse_decl; ds = parse_decls >] -> d::ds
| [< '(_, Kwd "/*@"); ds = parse_pure_decls; '(_, Kwd "@*/"); ds' = parse_decls >] -> ds @ ds'
| [< >] -> []
and
  parse_decl = parser
  [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, fs)
  | [< t = parse_type_suffix l s; d = parse_func_rest Regular (Some t) >] -> d
  >] -> d
| [< t = parse_return_type; d = parse_func_rest Regular t >] -> d
and
  parse_pure_decls = parser
  [< d = parse_pure_decl; ds = parse_pure_decls >] -> d::ds
| [< >] -> []
and
  parse_pure_decl = parser
  [< '(l, Kwd "inductive"); '(_, Ident i); '(_, Kwd "="); cs = parse_ctors; '(_, Kwd ";") >] -> Inductive (l, i, cs)
| [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> d
| [< '(l, Kwd "predicate"); '(_, Ident g); '(_, Kwd "("); ps = parse_paramlist; '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); >] -> PredDecl (l, g, ps, p)
| [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest Lemma t >] -> d
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
  [< '(_, Kwd "/*@"); '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/"); '(_, Kwd "/*@"); '(_, Kwd "ensures"); q = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> Some (p, q)
| [< '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "ensures"); q = parse_pred; '(_, Kwd ";") >] -> Some (p, q)
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
  [< '(l, Kwd "/*@"); s = parse_stmt; '(_, Kwd "@*/") >] -> PureStmt (l, s)
| [< '(l, Kwd "if"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); b1 = parse_block; '(_, Kwd "else"); b2 = parse_block >] -> IfStmt (l, e, b1, b2)
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); sscs = parse_switch_stmt_clauses; '(_, Kwd "}") >] -> SwitchStmt (l, e, sscs)
| [< '(l, Kwd "open"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Open (l, g, es) | _ -> raise (Stream.Error "Body of open statement must be call expression."))
| [< '(l, Kwd "close"); e = parse_expr; '(_, Kwd ";") >] ->
  (match e with CallExpr (_, g, es) -> Close (l, g, es) | _ -> raise (Stream.Error "Body of close statement must be call expression."))
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "/*@"); '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/"); b = parse_block >] -> WhileStmt (l, e, p, b)
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
  [< '(l, Kwd "&*&"); p2 = parse_pred >] -> Sep (l, p1, p2)
| [< >] -> p1
and
  parse_pred0 = parser
  [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_pred_clauses; '(_, Kwd "}") >] -> SwitchPred (l, e, cs)
| [< '(l, Kwd "emp") >] -> EmpPred l
| [< '(_, Kwd "("); p = parse_pred; '(_, Kwd ")") >] -> p
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
| [< '(l, Int i) >] -> IntLit (l, i)
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
    with Stream.Error msg -> raise (Stream.Error (string_of_loc (loc()) ^ ": " ^ msg))
  with ex -> close_in c; raise ex

let flatmap f xs = List.concat (List.map f xs)

let rec try_assoc x xys =
  match xys with
    [] -> None
  | (x', y)::xys when x' = x -> Some y
  | _::xys -> try_assoc x xys

let startswith s s0 =
  String.length s0 <= String.length s && String.sub s 0 (String.length s0) = s0

let theory = [
  "(DISTINCT true_ false_)";
  "(FORALL (e1 e2) (EQ (IF true_ e1 e2) e1))";
(*  "(FORALL (e1 e2) (EQ (IF false_ e1 e2) e2))";   *)
  "(FORALL (b e1 e2) (IMPLIES (NEQ b true_) (EQ (IF b e1 e2) e2)))";   (* The evil case split axiom. *)
  "(FORALL (e1 e2) (IFF (EQ (== e1 e2) true_) (EQ e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (!= e1 e2) true_) (NEQ e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (le e1 e2) true_) (<= e1 e2)))";
  "(FORALL (e1 e2) (IFF (EQ (lt e1 e2) true_) (< e1 e2)))"
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

let rec pprint_t t =
  let rec iter level t =
    let (l, s) =
      match t with
        Int n -> (0, string_of_int n)
      | Symb s -> (0, s)
      | FunApp ("*", [t1; t2]) -> (20, iter 20 t1 ^ " * " ^ iter 20 t2)
      | FunApp ("/", [t1; t2]) -> (20, iter 20 t1 ^ " / " ^ iter 10 t2)
      | FunApp ("+", [t1; t2]) -> (30, iter 30 t1 ^ " + " ^ iter 30 t2)
      | FunApp ("-", [t1; t2]) -> (30, iter 30 t1 ^ " - " ^ iter 20 t2)
      | FunApp ("==", [t1; t2]) -> (40, iter 30 t1 ^ " == " ^ iter 30 t2)
      | FunApp ("!=", [t1; t2]) -> (40, iter 30 t1 ^ " != " ^ iter 30 t2)
      | FunApp ("le", [t1; t2]) -> (40, iter 30 t1 ^ " le " ^ iter 30 t2)
      | FunApp ("lt", [t1; t2]) -> (40, iter 30 t1 ^ " lt " ^ iter 30 t2)
      | FunApp (g, ts) -> (0, g ^ "(" ^ pprint_ts ts ^ ")")
      | IfTerm (t1, t2, t3) -> (50, iter 40 t1 ^ " ? " ^ iter 50 t2 ^ " : " ^ iter 50 t3)
    in
    if l <= level then s else "(" ^ s ^ ")"
  in
  iter 100 t
and pprint_ts ts =
  match ts with [] -> "" | t::ts -> pprint_t t ^ (let rec iter' ts = match ts with [] -> "" | t::ts -> ", " ^ pprint_t t ^ iter' ts in iter' ts)

let slist ss =
  let rec args ss =
    match ss with
      [] -> ""
    | [s] -> s
    | (s::ss) -> s ^ " " ^ args ss
  in
    "(" ^ args ss ^ ")"

let pretty_print f =
  let rec iter level f =
    let (l, s) =
      match f with
        True -> (100, "TRUE")
      | PredApp (p, [t1; t2]) -> (100, pprint_t t1 ^ " " ^ p ^ " " ^ pprint_t t2)
      | Eq (t1, t2) -> (100, pprint_t t1 ^ " EQ " ^ pprint_t t2)
      | Not f -> (100, "NOT " ^ iter 100 f)
      | And (f1, f2) -> (110, iter 110 f1 ^ " AND " ^ iter 110 f2)
      | Or (f1, f2) -> (120, iter 120 f1 ^ " OR " ^ iter 120 f2)
      | Imp (f1, f2) -> (130, iter 120 f1 ^ " IMPLIES " ^ iter 130 f2)
      | Iff (f1, f2) -> (140, iter 100 f1 ^ " IFF " ^ iter 100 f2)
      | Forall (xs, f) -> (150, "FORALL " ^ slist xs ^ ". " ^ iter 150 f)
    in
    if l <= level then s else "(" ^ s ^ ")"
  in
  iter 200 f

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

(* Logical symbol generation:
 * Suffix   Category
 * _        constructor or fixpoint function
 * _tag     Constructor tag
 * _tagfunc Tag function
 * _proj    Projection function
 * _access  Accessor function
 * _0       variable
 * _size    sizeof value
 *)

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = slist (List.map (function (x, t) -> slist [x; simpt t]) env)

exception StaticError of loc * string

let static_error l msg = raise (StaticError (l, msg))

type heap = (string * term list) list
type env = (string * term) list
type context =
  Assuming of formula
| Executing of heap * env * loc * string

let string_of_heap h = slist (List.map (function (g, ts) -> slist (g::List.map simpt ts)) h)
  
let string_of_context c =
  match c with
    Assuming f -> "Assuming " ^ pretty_print f
  | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s

exception SymbolicExecutionError of context list * formula * loc * string

let rec eval env e =
  let ev = eval env in
  match e with
    Var (l, x) -> (match try_assoc x env with None -> (* It's a constructor *) Symb (x ^ "_") | Some t -> t)
  | Operation (l, op, es) -> (match es with [] -> Symb op | _ -> FunApp (op, List.map ev es))
  | IntLit (l, n) -> Int n
(*  | Read (l, e, f) ->  *)
  | CallExpr (l, g, pats) -> FunApp (g ^ "_", List.map (function (LitPat e) -> ev e) pats)
  | IfExpr (l, e1, e2, e3) -> IfTerm (ev e1, ev e2, ev e3)
(*  | SwitchExpr (l, e, cs) *)
  | SizeofExpr (l, t) ->
    match t with
      TypeName (_, tn) -> Symb (tn ^ "_size")
    | PtrType (_, tn) -> Symb "ptrsize"

let check_ghost ghostenv l e =
  let rec iter e =
    match e with
      Var (l, x) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context."
    | Operation (l, _, es) -> List.iter iter es
    | CallExpr (l, _, pats) -> List.iter (function LitPat e -> iter e | _ -> ()) pats
    | IfExpr (l, e1, e2, e3) -> (iter e1; iter e2; iter e3)
    | _ -> ()
  in
  iter e

let rec exptrue env e =
  let etrue = exptrue env in
  let ev = eval env in
  match e with
    Operation (_, "==", [e1; e2]) -> Eq (ev e1, ev e2)
  | Operation (_, "!=", [e1; e2]) -> Not (Eq (ev e1, ev e2))
  | Operation (_, "le", [e1; e2]) -> PredApp ("<=", [ev e1; ev e2])
  | Operation (_, "lt", [e1; e2]) -> PredApp ("<", [ev e1; ev e2])
  | Operation (_, "&&", [e1; e2]) -> And (etrue e1, etrue e2)
  | _ -> Eq (ev e, Symb "true_")

let zip xs ys =
  let rec iter xs ys zs =
    match (xs, ys) with
      ([], []) -> Some (List.rev zs)
    | (x::xs, y::ys) -> iter xs ys ((x, y)::zs)
    | _ -> None
  in
  iter xs ys []

let verify_program verbose path =

  let verbose_print_endline s = if verbose then print_endline s else () in
  let verbose_print_string s = if verbose then print_string s else () in

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
  
  let get_unique_var_symb s = get_unique_symb (s ^ "_") in

  let (simp_in, simp_out) = Unix.open_process "z3 /si" in
  
  let imap f xs =
    let rec imapi i xs =
      match xs with
        [] -> []
      | x::xs -> f i x::imapi (i + 1) xs
    in
    imapi 0 xs
  in
  
  let Program ds = read_program path in
  
  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds)::ds ->
        if List.mem_assoc sn sdm then
          static_error l "Duplicate struct name."
        else
          iter ((sn, (l, fds))::sdm) ds
      | _::ds -> iter sdm ds
    in
    iter [] ds
  in
  
  let structmap =
    List.map
      (fun (sn, (l, fds)) ->
         let rec iter fmap fds =
           match fds with
             [] -> (sn, (l, List.rev fmap))
           | Field (lf, t, f)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else (
               let _ =
                 match t with
                   TypeName (_, "int") -> ()
                 | PtrType (lt, sn) ->
                   if List.mem_assoc sn structdeclmap then
                     ()
                   else
                     static_error lt "No such struct."
               in
               iter ((f, (lf, t))::fmap) fds
             )
         in
         iter [] fds
      )
      structdeclmap
  in
  
  let dummy_loc = ("prelude", 0, 0) in
  
  let inductivedeclmap =
    let rec iter idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, ctors))::ds ->
        if i = "int" || List.mem_assoc i idm then
          static_error l "Duplicate datatype name."
        else
          iter ((i, (l, ctors))::idm) ds
      | _::ds -> iter idm ds
    in
    iter [("bool", (dummy_loc, []))] ds
  in
  
  let check_pure_type t =
    match t with
      TypeName (l, tn) ->
      if not (tn = "int" || List.mem_assoc tn inductivedeclmap) then
        static_error l "No such datatype."
    | PtrType (l, sn) ->
      if not (List.mem_assoc sn structmap) then
        static_error l "No such struct."
  in 
  
  let boolt = TypeName (dummy_loc, "bool") in
  let intt = TypeName (dummy_loc, "int") in
  
  let string_of_type t =
    match t with
      TypeName (_, tn) -> tn
    | PtrType (_, tn) -> "struct " ^ tn ^ " *"
  in
  
  let (inductivemap, purefuncmap) =
    let rec iter imap pfm ds =
      match ds with
        [] -> (List.rev imap, List.rev pfm)
      | Inductive (l, i, ctors)::ds ->
        let rec citer ctormap pfm ctors =
          match ctors with
            [] -> iter ((i, (l, List.rev ctormap))::imap) pfm ds
          | Ctor (lc, cn, ts)::ctors ->
            if List.mem_assoc cn pfm then
              static_error lc "Duplicate pure function name."
            else (
              List.iter check_pure_type ts;
              let entry = (cn, (lc, ts)) in
              citer ((cn, (lc, ts))::ctormap) ((cn, (lc, TypeName (l, i), ts))::pfm) ctors
            )
        in
        citer [] pfm ctors
      | Func (l, Fixpoint, rto, g, ps, contract, body)::ds ->
        let _ =
          if List.mem_assoc g pfm then static_error l "Duplicate pure function name."
        in
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void."
          | Some rt -> (check_pure_type rt; rt)
        in
        let _ =
          match contract with
            None -> ()
          | Some _ -> static_error l "Fixpoint functions cannot have a contract."
        in
        let pmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (t, p)::ps ->
              let _ = if List.mem_assoc p pmap then static_error l "Duplicate parameter name." in
              let _ = check_pure_type t in
              iter ((p, t)::pmap) ps
          in
          iter [] ps
        in
        let _ = 
          match body with
            [SwitchStmt (ls, e, cs)] -> (
            match e with
              Var (l, x) -> (
              match try_assoc x pmap with
                None -> static_error l "Fixpoint function must switch on a parameter."
              | Some (TypeName (lt, "int")) -> static_error ls "Cannot switch on int."
              | Some (TypeName (lt, i)) -> (
                match try_assoc i imap with
                  None -> static_error ls "Switch statement cannot precede inductive declaration."
                | Some (l, ctormap) ->
                  let rec iter ctormap cs =
                    match cs with
                      [] ->
                      let _ = 
                        match ctormap with
                          [] -> ()
                        | (cn, _)::_ ->
                          static_error ls ("Missing case: '" ^ cn ^ "'.")
                      in ()
                    | SwitchStmtClause (lc, cn, xs, body)::cs -> (
                      match try_assoc cn ctormap with
                        None -> static_error lc "No such constructor."
                      | Some (_, ts) ->
                        let xmap =
                          let rec iter xmap ts xs =
                            match (ts, xs) with
                              ([], []) -> xmap
                            | (t::ts, x::xs) ->
                              let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." in
                              iter ((x, t)::xmap) ts xs
                            | ([], _) -> static_error lc "Too many pattern variables."
                            | _ -> static_error lc "Too few pattern variables."
                          in
                          iter [] ts xs
                        in
                        let tenv = xmap @ pmap in
                        let body =
                          match body with
                            [ReturnStmt (_, Some e)] -> e
                          | _ -> static_error lc "Body of switch clause must be a return statement with a result expression."
                        in
                        let rec check e =
                          match e with
                            Var (l, x) -> (
                            match try_assoc x tenv with
                              None -> (
                                match try_assoc x pfm with
                                  Some (_, t, []) -> t
                                | _ -> static_error l "No such variable or constructor."
                              )
                            | Some t -> t
                            )
                          | Operation (l, ("==" | "!="), [e1; e2]) ->
                            let t = check e1 in
                            let _ = checkt e2 t in
                            boolt
                          | Operation (l, ("le" | "lt"), [e1; e2]) ->
                            let _ = checkt e1 intt in
                            let _ = checkt e2 intt in
                            boolt
                          | Operation (l, ("+" | "-"), [e1; e2]) ->
                            let _ = checkt e1 intt in
                            let _ = checkt e2 intt in
                            intt
                          | IntLit (l, n) -> intt
                          | CallExpr (l, g', pats) -> (
                            match try_assoc g' pfm with
                              Some (l, t, ts) -> (
                              match zip pats ts with
                                None -> static_error l "Incorrect argument count."
                              | Some pts -> (
                                List.iter (fun (pat, t) ->
                                  match pat with
                                    LitPat e -> checkt e t
                                  | _ -> static_error l "Patterns are not allowed here."
                                ) pts;
                                t
                                )
                              )
                            | None ->
                              if g' = g then
                                match zip pmap pats with
                                  None -> static_error l "Incorrect argument count."
                                | Some pts ->
                                  let _ =
                                    List.iter (fun ((p, t), pat) ->
                                      match pat with
                                        LitPat e -> checkt e t
                                      | _ -> static_error l "Patterns are not allowed here."
                                    ) pts
                                  in
                                  let _ =
                                    match flatmap (function ((p, t), LitPat e) -> if p = x then [e] else []) pts with
                                      [Var (l, x)] when List.mem_assoc x xmap -> ()
                                    | _ -> static_error l "Inductive argument of recursive call must be switch clause pattern variable."
                                  in
                                  rt
                              else
                                static_error l "No such pure function."
                            )
                          | IfExpr (l, e1, e2, e3) ->
                            let _ = checkt e1 boolt in
                            let t = check e2 in
                            let _ = checkt e3 t in
                            t
                          | e -> static_error (expr_loc e) "Expression form not allowed in fixpoint function body."
                        and checkt e t0 =
                          let t = check e in
                          match (t, t0) with
                            (TypeName (_, tn), TypeName (_, tn')) when tn = tn' -> ()
                          | (PtrType (_, sn), PtrType (_, sn')) when sn = sn' -> ()
                          | _ -> static_error (expr_loc e) ("Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
                        in
                        let _ = checkt body rt in
                        iter (List.remove_assoc cn ctormap) cs
                      )
                  in
                  iter ctormap cs
                )
              | _ -> static_error l "Cannot switch on a pointer type."
              )
            )
          | _ -> static_error l "Body of fixpoint function must be switch statement."
        in
        iter imap ((g, (l, rt, List.map (fun (p, t) -> t) pmap))::pfm) ds
      | _::ds -> iter imap pfm ds
    in
    iter [("bool", (dummy_loc, [("true", (dummy_loc, [])); ("false", (dummy_loc, []))]))] [("true", (dummy_loc, boolt, [])); ("false", (dummy_loc, boolt, []))] ds
  in
  
  let indaxs =
    flatmap
    (function
       Inductive (l, i, cs) ->
       let tags = List.map (function (Ctor (l, c, ps)) -> c ^ "_tag") cs in
       let da = slist ("DISTINCT" :: tags) in
       let tagaxs =
         List.map
           (function (Ctor (l, c, ps)) ->
              match ps with
                [] -> slist ["EQ"; slist [i ^ "_tagfunc"; c ^ "_"]; c ^ "_tag"]
              | _ ->
                let xs = imap (fun i t -> "x" ^ string_of_int i) ps in
                slist ["FORALL"; slist xs; slist ["PATS"; slist ((c ^ "_") :: xs)]; slist ["EQ"; slist [i ^ "_tagfunc"; slist ((c ^ "_") :: xs)]; c ^ "_tag"]]
           )
           cs
       in
       let projaxs =
         flatmap
           (function (Ctor (l, c, ps)) ->
              let xs = imap (fun i t -> "x" ^ string_of_int i) ps in
              List.map
                (fun x ->
                   slist ["FORALL"; slist xs; slist ["PATS"; slist ((c ^ "_") :: xs)]; slist ["EQ"; slist [c ^ "_proj" ^ x; slist ((c ^ "_") :: xs)]; x]]
                )
                xs
           )
           cs
       in
       da :: tagaxs @ projaxs
     | Func (l, Fixpoint, t, g, ps, _, [SwitchStmt (_, Var (_, x), cs)]) ->
       let penv = List.map (fun (t, x) -> (x, Symb (x ^ "_0"))) ps in
       List.map
         (function (SwitchStmtClause (lc, cn, pats, [ReturnStmt (_, Some e)])) ->
            let patenv = List.map (fun x -> (x, Symb (x ^ "_1"))) pats in
            let patvals = List.map (fun x -> x ^ "_1") pats in
            let xs' = flatmap (fun (t, p) -> if p = x then patvals else [p ^ "_0"]) ps in
            let csymb = cn ^ "_" in
            let args = List.map (fun (t, p) -> if p = x then match pats with [] -> csymb | _ -> slist (csymb :: patvals) else p ^ "_0") ps in
            let gsymb = g ^ "_" in
            let env = patenv @ penv in
            let body = slist ["EQ"; slist (gsymb :: args); simpt (eval env e)] in
            match xs' with
              [] -> body
            | _ -> slist ["FORALL"; slist xs'; slist ["PATS"; slist (gsymb :: args)]; body]
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
  
  let contextStack = ref ([]: context list) in
  
  let push_context msg = let _ = contextStack := msg::!contextStack in () in
  let pop_context () = let _ = let (h::t) = !contextStack in contextStack := t in () in
    
  let with_context msg cont =
    push_context msg;
    cont();
    pop_context();
    ()
  in
  
  let assume phi cont =
    let s = simp phi in
    push_context (Assuming phi);
    bg_push s;
    (if not (query_formula (Not True)) then cont());
    pop_context ();
    send_command "(BG_POP)";
    ()
  in
  
  let assert_formula phi h env l msg cont =
    (if not (query_formula phi) then raise (SymbolicExecutionError (!contextStack, phi, l, msg)));
    cont()
  in
  
  let assert_false h env l msg =
    assert_formula (Not True) h env l msg (fun _ -> ())
  in
  
  let success() = () in
  
  let branch cont1 cont2 =
    cont1();
    cont2()
  in
  
  let evalpat ghostenv env pat cont =
    match pat with
      LitPat e -> cont ghostenv env (eval env e)
    | VarPat x -> let t = get_unique_var_symb x in cont (x::ghostenv) (update env x t) t
    | DummyPat -> let t = get_unique_symb "dummy" in cont ghostenv env t
  in
  
  let rec evalpats ghostenv env pats cont =
    match pats with
      [] -> cont ghostenv env []
    | pat::pats -> evalpat ghostenv env pat (fun ghostenv env t -> evalpats ghostenv env pats (fun ghostenv env ts -> cont ghostenv env (t::ts)))
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
  
  let rec assume_pred h ghostenv env p cont =
    with_context (Executing (h, env, pred_loc p, "Assuming predicate")) (fun _ ->
    let ev = eval env in
    let etrue = exptrue env in
    match p with
    | Access (l, e, f, rhs) -> let te = ev e in evalpat ghostenv env rhs (fun ghostenv env t -> assume_field h f te t (fun h -> cont h ghostenv env))
    | CallPred (l, g, pats) -> evalpats ghostenv env pats (fun ghostenv env ts -> cont ((g, ts)::h) ghostenv env)
    | ExprPred (l, e) -> assume (etrue e) (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) -> assume_pred h ghostenv env p1 (fun h ghostenv env -> assume_pred h ghostenv env p2 cont)
    | IfPred (l, e, p1, p2) -> branch (fun _ -> assume (etrue e) (fun _ -> assume_pred h ghostenv env p1 cont)) (fun _ -> assume (Not (etrue e)) (fun _ -> assume_pred h ghostenv env p2 cont))
    | SwitchPred (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          branch
            (fun _ ->
               let xts = List.map (fun x -> (x, get_unique_var_symb x)) pats in
               assume (Eq (t, FunApp(cn ^ "_", List.map (fun (x, t) -> t) xts))) (fun _ -> assume_pred h (pats @ ghostenv) (xts @ env) p cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env
    )
  in
  
  let definitely_equal t1 t2 =
    if t1 = t2 then true else query_formula (Eq (t1, t2))
  in
  
  let match_chunk ghostenv env g pats (g', ts0) =
    let rec iter ghostenv env pats ts =
      match (pats, ts) with
        (LitPat e::pats, t::ts) -> if definitely_equal (eval env e) t then iter ghostenv env pats ts else None
      | (VarPat x::pats, t::ts) -> iter (x::ghostenv) (update env x t) pats ts
      | (DummyPat::pats, t::ts) -> iter ghostenv env pats ts
      | ([], []) -> Some (ts0, ghostenv, env)
    in
      if g = g' then
        iter ghostenv env pats ts0
      else
        None
  in
  
  let assert_chunk h ghostenv env l g pats cont =
    let rec iter hprefix h =
      match h with
        [] -> []
      | chunk::h ->
        let matches =
          match match_chunk ghostenv env g pats chunk with
            None -> []
          | Some (ts, ghostenv, env) -> [(hprefix @ h, ts, ghostenv, env)]
        in
          matches @ iter (chunk::hprefix) h
    in
    match iter [] h with
      [] -> assert_false h env l "No matching heap chunks."
    | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
    | _ -> assert_false h env l "Multiple matching heap chunks."
  in
  
  let rec assert_pred h ghostenv env p cont =
    with_context (Executing (h, env, pred_loc p, "Asserting predicate")) (fun _ ->
    let ev = eval env in
    let etrue = exptrue env in
    match p with
    | Access (l, e, f, rhs) ->
      assert_chunk h ghostenv env l ("field_" ^ f) [LitPat e; rhs] (fun h ts ghostenv env -> cont h ghostenv env)
    | CallPred (l, g, pats) ->
      assert_chunk h ghostenv env l g pats (fun h ts ghostenv env -> cont h ghostenv env)
    | ExprPred (l, e) ->
      assert_formula (etrue e) h env l "Expression is false." (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) ->
      assert_pred h ghostenv env p1 (fun h ghostenv env -> assert_pred h ghostenv env p2 cont)
    | IfPred (l, e, p1, p2) ->
      branch
        (fun _ ->
           assume (etrue e) (fun _ ->
             assert_pred h ghostenv env p1 cont))
        (fun _ ->
           assume (Not (etrue e)) (fun _ ->
             assert_pred h ghostenv env p2 cont))
    | SwitchPred (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          let xts = List.map (fun x -> (x, get_unique_var_symb x)) pats in
          branch
            (fun _ -> assume (Eq (t, FunApp (cn ^ "_", List.map (fun (x, t) -> t) xts))) (fun _ -> assert_pred h (pats @ ghostenv) (xts @ env) p cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env
    )
  in

  let rec block_assigned_variables ss =
    match ss with
      [] -> []
    | s::ss -> assigned_variables s @ block_assigned_variables ss
  and assigned_variables s =
    match s with
      Assign (l, x, e) -> [x]
    | IfStmt (l, e, ss1, ss2) -> block_assigned_variables ss1 @ block_assigned_variables ss2
    | SwitchStmt (l, e, cs) -> static_error l "Switch statements inside loops are not supported."
    | WhileStmt (l, e, p, ss) -> block_assigned_variables ss
    | _ -> []
  in
  
  let get_field h t f l cont =
    assert_chunk h [] [("x", t)] l ("field_" ^ f) [LitPat (Var (dummy_loc, "x")); VarPat "y"] (fun h ts ghostenv env ->
      cont h (lookup env "y"))
  in
  
  let predmap =
    let rec iter predmap ds =
      match ds with
        [] -> predmap
      | PredDecl (l, pn, ps, p)::ds ->
        let _ = if List.mem_assoc pn predmap then static_error l "Duplicate predicate name." in
        let _ = if startswith pn "field_" || startswith pn "malloc_block_" then static_error l "A predicate name cannot start with 'field_' or 'malloc_block_'." in
        iter ((pn, (ps, p))::predmap) ds
      | _::ds -> iter predmap ds
    in
    iter [] ds
  in

  let rec verify_stmt pure leminfo sizemap tenv ghostenv h env s tcont =
    let l = stmt_loc s in
    let ev e = let _ = if not pure then check_ghost ghostenv l e in eval env e in
    let etrue e = let _ = if not pure then check_ghost ghostenv l e in exptrue env e in
    let cont = tcont sizemap tenv ghostenv in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context."
    in
    let call_stmt l xo g pats =
      let ts = List.map (function (LitPat e) -> ev e) pats in
      let fds = flatmap (function (Func (lg, k, tr, g', ps, Some (pre, post), _)) when g = g' && k != Fixpoint -> [(k, ps, pre, post)] | _ -> []) ds in
      (
      match fds with
        [] -> (
        match try_assoc g purefuncmap with
          None -> static_error l "No such function."
        | Some _ -> (
          match xo with
            None -> static_error l "Cannot write call of pure function as statement."
          | Some x ->
            let _ = check_assign l x in
            cont h (update env x (FunApp (g ^ "_", ts)))
          )
        )
      | [(k, ps, pre, post)] ->
        let _ = if pure && k = Regular then static_error l "Cannot call regular methods in a pure context." in
        let ys = List.map (function (t, p) -> p) ps in
        let Some env' = zip ys ts in
        assert_pred h ghostenv env' pre (fun h ghostenv' env' ->
          let _ =
            match leminfo with
              None -> ()
            | Some (lems, g0, indinfo) ->
              if List.mem g lems then
                ()
              else if g = g0 then
                let rec nonempty h =
                  match h with
                    [] -> false
                  | (p, ts)::_ when startswith p "field_" -> true
                  | _::h -> nonempty h
                in
                if nonempty h then
                  ()
                else (
                  match indinfo with
                    None -> assert_false h env l "Recursive lemma call does not decrease the heap and there is no inductive parameter."
                  | Some x -> (
                    match try_assoc (List.assoc x env') sizemap with
                      Some k when k < 0 -> ()
                    | _ -> assert_false h env l "Recursive lemma call does not decrease the heap or the inductive parameter."
                    )
                )
              else
                static_error l "A lemma can call only preceding lemmas or itself."
          in
          let r = get_unique_symb "result" in
          let env'' = update env' "result" r in
          assume_pred h ghostenv' env'' post (fun h _ _ ->
            let env =
              match xo with
                None -> env
              | Some x ->
                let _ = check_assign l x in
                update env x r
            in
            cont h env)
        )
      )
    in
    match s with
      PureStmt (l, s) ->
      verify_stmt true leminfo sizemap tenv ghostenv h env s tcont
    | Assign (l, x, Read (lr, e, f)) ->
      let _ = check_assign l x in
      let t = ev e in
      get_field h t f l (fun _ v ->
        cont h (update env x v))
    | CallStmt (l, "assert", [e]) ->
      assert_formula (etrue e) h env l "Assertion failure." (fun _ -> cont h env)
    | Assign (l, x, CallExpr (lc, "malloc", [LitPat (SizeofExpr (lsoe, TypeName (ltn, tn)))])) ->
      let _ = check_assign l x in
      let [fds] = flatmap (function (Struct (ls, sn, fds)) when sn = tn -> [fds] | _ -> []) ds in
      let result = get_unique_symb "block" in
      let rec iter h fds =
        match fds with
          [] -> cont (h @ [("malloc_block_" ^ tn, [result])]) (update env x result)
        | Field (lf, t, f)::fds -> assume_field h f result (get_unique_symb "value") (fun h -> iter h fds)
      in
      iter h fds
    | CallStmt (l, "free", [Var (lv, x)]) ->
      let _ = if pure then static_error l "Cannot call a non-pure function from a pure context." in
      let (PtrType (_, tn)) = tenv x in
      let [fds] = flatmap (function (Struct (ls, sn, fds)) when sn = tn -> [fds] | _ -> []) ds in
      let rec iter h fds =
        match fds with
          [] -> cont h env
        | (Field (lf, t, f))::fds -> get_field h (lookup env x) f l (fun h _ -> iter h fds)
      in
      assert_chunk h ghostenv env l ("malloc_block_" ^ tn) [LitPat (Var (lv, x))] (fun h _ _ _ -> iter h fds)
    | Assign (l, x, CallExpr (lc, g, pats)) ->
      call_stmt l (Some x) g pats
    | Assign (l, x, e) ->
      let _ = if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context." in
      cont h (update env x (ev e))
    | DeclStmt (l, t, x, e) ->
      let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
      verify_stmt pure leminfo sizemap (fun y -> if y = x then t else tenv y) ghostenv h env (Assign (l, x, e)) tcont
    | Write (l, e, f, rhs) ->
      let _ = if pure then static_error l "Cannot write in a pure context." in
      let t = ev e in
      get_field h t f l (fun h _ ->
        cont (("field_" ^ f, [t; ev rhs])::h) env)
    | CallStmt (l, g, es) ->
      call_stmt l None g (List.map (fun e -> LitPat e) es)
    | IfStmt (l, e, ss1, ss2) ->
      let t = ev e in
      branch
        (fun _ -> assume (Eq (t, Symb "true_")) (fun _ -> verify_cont pure leminfo sizemap tenv ghostenv h env ss1 tcont))
        (fun _ -> assume (Eq (t, Symb "false_")) (fun _ -> verify_cont pure leminfo sizemap tenv ghostenv h env ss2 tcont))
    | SwitchStmt (l, e, cs) ->
      let t = ev e in
      let rec iter cs =
        match cs with
          [] -> success()
        | SwitchStmtClause (lc, cn, pats, ss)::cs ->
          let xts = List.map (fun x -> (x, get_unique_var_symb x)) pats in
          let sizemap =
            match try_assoc t sizemap with
              None -> sizemap
            | Some k -> List.map (fun (x, t) -> (t, k - 1)) xts @ sizemap
          in
          branch
            (fun _ -> assume (Eq (t, FunApp (cn ^ "_", List.map (fun (x, t) -> t) xts))) (fun _ -> verify_cont pure leminfo sizemap tenv (pats @ ghostenv) h (xts @ env) ss tcont))
            (fun _ -> iter cs)
      in
      iter cs
    | Open (l, g, pats) ->
      assert_chunk h ghostenv env l g pats (fun h ts ghostenv env ->
        let [(lpd, ps, p)] = flatmap (function PredDecl (lpd, g', ps, p) when g = g' -> [(lpd, ps, p)] | _ -> []) ds in
        let ys = List.map (function (t, p) -> p) ps in
        let Some env' = zip ys ts in
        assume_pred h ghostenv env' p (fun h _ _ ->
          cont h env))
    | Close (l, g, pats) ->
      let ts = List.map (function LitPat e -> ev e) pats in
      let [(lpd, ps, p)] = flatmap (function PredDecl (lpd, g', ps, p) when g = g' -> [(lpd, ps, p)] | _ -> []) ds in
      let ys = List.map (function (t, p) -> p) ps in
      let Some env' = zip ys ts in
      assert_pred h ghostenv env' p (fun h _ _ ->
        cont ((g, ts)::h) env)
    | ReturnStmt (l, Some e) ->
      cont h (update env "#result" (ev e))
    | ReturnStmt (l, None) -> cont h env
    | WhileStmt (l, e, p, ss) ->
      let _ = if pure then static_error l "Loops are not yet supported in a pure context." in
      let xs = block_assigned_variables ss in
      assert_pred h ghostenv env p (fun h ghostenv env ->
        let ts = List.map get_unique_var_symb xs in
        let Some bs = zip xs ts in
        let env = bs @ env in
        branch
          (fun _ ->
             assume_pred [] ghostenv env p (fun h ghostenv env ->
               assume (exptrue env e) (fun _ ->
                 verify_cont pure leminfo sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env ->
                   assert_pred h ghostenv env p (fun h _ _ ->
                     match h with
                       [] -> success()
                     | _ -> assert_false h env l "Loop leaks heap chunks."
                   )
                 )
               )
             )
          )
          (fun _ ->
             assume_pred h ghostenv env p (fun h ghostenv env ->
               assume (Not (exptrue env e)) (fun _ ->
                 cont h env)))
      )
  and
    verify_cont pure leminfo sizemap tenv ghostenv h env ss cont =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        verify_stmt pure leminfo sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          verify_cont pure leminfo sizemap tenv ghostenv h env ss cont)
      )
  in

  let rec verify_decls lems ds =
    match ds with
    | [] -> ()
    | Func (l, Fixpoint, _, _, _, _, _)::ds -> verify_decls lems ds
    | Func (l, k, rt, g, ps, Some (pre, post), ss)::ds ->
      let env = List.map (function (t, p) -> (p, Symb (p ^ "_0"))) ps in
      let (sizemap, indinfo) =
        match ss with
          [SwitchStmt (_, Var (_, x), _)] -> (
          match try_assoc x env with
            None -> ([], None)
          | Some t -> ([(t, 0)], Some x)
          )
        | _ -> ([], None)
      in
      let pts = List.map (function (t, p) -> (p, t)) ps in
      let tenv x = List.assoc x pts in
      let (in_pure_context, leminfo, lems') =
        if k = Lemma then
          (true, Some (lems, g, indinfo), g::lems)
        else
          (false, None, lems)
      in
      let _ =
        assume_pred [] [] env pre (fun h ghostenv env ->
          verify_cont in_pure_context leminfo sizemap tenv [] h env ss (fun _ _ _ h env' ->
            let get_env_post cont =
              match rt with
                None -> cont env
              | Some t -> (
                match try_assoc "#result" env' with
                  None -> assert_false h env l "Function does not specify a return value."
                | Some t -> cont (update env "result" t)
                )
            in
            get_env_post (fun env_post ->
            assert_pred h ghostenv env_post post (fun h _ _ ->
              with_context (Executing (h, env, l, "Checking emptyness.")) (fun _ ->
              match h with
                [] -> success()
              | _ -> assert_false h env l "Function leaks heap chunks."
              )
            )
            )
          )
        )
      in
      verify_decls lems' ds
    | _::ds -> verify_decls lems ds
  in
  
  let _ = verify_decls [] ds in
  print_endline "0 errors found"

open Tk

let browse_trace path ctxts_lifo =
  let root = openTk() in
  let srcFrame = Frame.create root in
  let srcText = Text.create srcFrame ~font:"Courier 10" ~wrap:`None in
  let srcXScroll = Scrollbar.create srcFrame ~orient:`Horizontal ~command:(Text.xview srcText) in
  let srcYScroll = Scrollbar.create srcFrame ~orient:`Vertical ~command:(Text.yview srcText) in
  let _ = Text.configure srcText ~xscrollcommand:(Scrollbar.set srcXScroll) in
  let _ = Text.configure srcText ~yscrollcommand:(Scrollbar.set srcYScroll) in
  let _ =
    let chan = open_in path in
    let buf = String.create 60000 in
    let rec iter () =
      let result = input chan buf 0 60000 in
      if result = 0 then () else (Text.insert (`End, []) (String.sub buf 0 result) srcText; iter())
    in
    let _ = iter() in
    let _ = close_in chan in
    ()
  in
  let _ = grid [srcText] ~row:0 ~column:0 ~sticky:"nsew" in
  let _ = grid [srcXScroll] ~row:1 ~column:0 ~sticky:"ew" in
  let _ = grid [srcYScroll] ~row:0 ~column:1 ~sticky:"ns" in
  let _ = Grid.column_configure srcFrame 0 ~weight:1 in
  let _ = Grid.row_configure srcFrame 0 ~weight:1 in
  let _ = Text.configure srcText ~state:`Disabled in
  let bottomFrame = Frame.create root in
  let create_listbox parent =
    let frame = Frame.create parent in
    let lb = Listbox.create frame in
    let sx = Scrollbar.create frame ~orient:`Horizontal ~command:(Listbox.xview lb) in
    let sy = Scrollbar.create frame ~orient:`Vertical ~command:(Listbox.yview lb) in
    let _ = Listbox.configure lb ~xscrollcommand:(Scrollbar.set sx) in
    let _ = Listbox.configure lb ~yscrollcommand:(Scrollbar.set sy) in
    let _ = grid [lb] ~row:0 ~column:0 ~sticky:"nsew" in
    let _ = grid [sx] ~row:1 ~column:0 ~sticky:"ew" in
    let _ = grid [sy] ~row:0 ~column:1 ~sticky:"ns" in
    let _ = Grid.row_configure frame 0 ~weight:1 in
    let _ = Grid.column_configure frame 0 ~weight:1 in
    (frame, lb)
  in
  let (steplistFrame, stepList) = create_listbox bottomFrame in
  let (assumptionsFrame, assumptionsList) = create_listbox bottomFrame in
  let _ = Listbox.configure assumptionsList ~takefocus:true in
  let (chunksFrame, chunksList) = create_listbox bottomFrame in
  let (envFrame, envList) = create_listbox bottomFrame in
  let ctxts_fifo = List.rev ctxts_lifo in
  let stepItems =
    let rec iter ass ctxts =
      match ctxts with
        [] -> []
      | Assuming phi::cs -> iter (phi::ass) cs
      | Executing (h, env, l, msg)::cs -> (ass, h, env, l, msg)::iter ass cs
    in
    iter [] ctxts_fifo
  in
  let _ = Listbox.insert stepList `End (List.map (fun (ass, h, env, l, msg) -> msg) stepItems) in
  let _ = grid [steplistFrame] ~row:0 ~column:0 ~sticky:"nsew" in
  let _ = grid [assumptionsFrame] ~row:0 ~column:1 ~sticky:"nsew" in
  let _ = grid [chunksFrame] ~row:0 ~column:2 ~sticky:"nsew" in
  let _ = grid [envFrame] ~row:0 ~column:3 ~sticky:"nsew" in
  let _ = Grid.column_configure bottomFrame 0 ~weight:1 in
  let _ = Grid.column_configure bottomFrame 1 ~weight:1 in
  let _ = Grid.column_configure bottomFrame 2 ~weight:1 in
  let _ = Grid.column_configure bottomFrame 3 ~weight:1 in
  let _ = Grid.row_configure bottomFrame 0 ~weight:1 in
  let _ = grid [srcFrame] ~row:0 ~column:0 ~sticky:"nsew" in
  let _ = grid [bottomFrame] ~row:1 ~column:0 ~sticky:"nsew" in
  let _ = Grid.column_configure root 0 ~weight:1 in
  let _ = Grid.row_configure root 0 ~weight:1 in
  let _ = Grid.row_configure root 0 ~weight:1 in
  let _ = bind stepList ~events:[`Virtual "ListboxSelect"] ~action:(fun _ ->
    let [`Num k] = Listbox.curselection stepList in
    let (ass, h, env, l, msg) = List.nth stepItems k in
    let (path, line, col) = l in
    let _ = Text.tag_delete srcText ["currentLine"] in
    let _ = Text.tag_add srcText ~tag:"currentLine" ~start:(`Linechar (line, col - 1), []) ~stop:(`Linechar (line, col), []) in
    let _ = Text.tag_configure srcText ~tag:"currentLine" ~background:`Yellow in
    let _ = Text.see srcText (`Linechar (line, col - 1), []) in
    let _ = Listbox.delete assumptionsList ~first:(`Num 0) ~last:`End in
    let _ = Listbox.insert assumptionsList `End (List.map (fun phi -> pretty_print phi) ass) in
    let _ = Listbox.delete chunksList ~first:(`Num 0) ~last:`End in
    let _ = Listbox.insert chunksList `End (List.map (fun (g, ts) -> g ^ "(" ^ pprint_ts ts ^ ")") h) in
    let _ = Listbox.delete envList ~first:(`Num 0) ~last:`End in
    let _ = Listbox.insert envList `End (List.map (fun (x, t) -> x ^ "=" ^ pprint_t t) env) in
    ()
  ) in
  mainLoop()

let _ =
  let print_msg path l msg =
    print_endline (path ^ string_of_loc l ^ ": " ^ msg)
  in
  let verify verbose path =
    try
      verify_program verbose path
    with
      StaticError (l, msg) -> print_msg path l msg
    | SymbolicExecutionError (ctxts, phi, l, msg) ->
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        (*
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_endline ("Failed query: " ^ simp phi) in
        let _ = print_msg path l msg in
        let _ = browse_trace path ctxts in
        ()
  in
  match Sys.argv with
    [| _; path |] -> verify false path
  | [| _; "-verbose"; path |] -> verify true path
  | _ ->
    print_endline "Verifast 0.2 for C";
    print_endline "Usage: verifast [-verbose] filepath";
    print_endline "Note: Requires z3.exe."

end
