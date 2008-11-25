open Proverapi
open Big_int

class stats =
  object (self)
    val mutable stmtsParsedCount = 0
    val mutable stmtExecCount = 0
    val mutable execStepCount = 0
    val mutable branchCount = 0
    val mutable proverCmdCount = 0
    val mutable proverQueryCount = 0
    
    method stmtParsed = stmtsParsedCount <- stmtsParsedCount + 1
    method stmtExec = stmtExecCount <- stmtExecCount + 1
    method execStep = execStepCount <- execStepCount + 1
    method branch = branchCount <- branchCount + 1
    method proverCmd = proverCmdCount <- proverCmdCount + 1
    method proverQuery = proverQueryCount <- proverQueryCount + 1
    
    method printStats =
      print_endline ("Statements parsed: " ^ string_of_int stmtsParsedCount);
      print_endline ("Statement executions: " ^ string_of_int stmtExecCount);
      print_endline ("Execution steps (including assertion production/consumption steps): " ^ string_of_int execStepCount);
      print_endline ("Branches: " ^ string_of_int branchCount);
      print_endline ("Prover commands: " ^ string_of_int proverCmdCount);
      print_endline ("Prover queries: " ^ string_of_int proverQueryCount)
  end

let stats = new stats

let readFile path =
  let chan = open_in path in
  let count = ref 0 in
  let rec iter () =
    let buf = String.create 60000 in
    let result = input chan buf 0 60000 in
    count := !count + result;
    if result = 0 then [] else (buf, result)::iter()
  in
  let chunks = iter() in
  let _ = close_in chan in
  let s = String.create !count in
  let rec iter2 chunks offset =
    match chunks with
      [] -> ()
    | (buf, size)::chunks ->
      String.blit buf 0 s offset size;
      iter2 chunks (offset + size)
  in
  iter2 chunks 0;
  s

type token =
    Kwd of string
  | Ident of string
  | Int of big_int
  | Float of float
  | String of string
  | Char of char
  | Eol

type srcpos = ((string * string) * int * int)
type loc = (srcpos * srcpos)

exception ParseException of loc * string

(* The lexer *)

let make_lexer keywords path stream reportKeyword =
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
  let token_srcpos = ref (path, -1, -1) in

  let current_srcpos() = (path, !line, Stream.count stream - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in

  let in_single_line_annotation = ref false in
  
  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  let ident_or_keyword id isAlpha =
    try let t = Hashtbl.find kwd_table id in if isAlpha then reportKeyword (current_loc()); t with
      Not_found -> Ident id
  and keyword_or_error c =
    let s = String.make 1 c in
    try Hashtbl.find kwd_table s with
      Not_found -> raise (Stream.Error ("Illegal character"))
  in
  let start_token() =
    tokenpos := Stream.count stream;
    token_srcpos := current_srcpos()
  in
  let new_loc_line strm__ =
      line := !line + 1;
      linepos := Stream.count strm__
  in
  let rec next_token (strm__ : _ Stream.t) =
    let new_line strm__ =
      new_loc_line strm__;
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        Some (Kwd "@*/")
      ) else
        Some Eol
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
    | Some '(' -> Stream.junk strm__; Some(ident_or_keyword "(" false)
    | Some
        ('!' | '%' | '&' | '$' | '#' | '+' | ':' | '<' | '=' | '>' |
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
            Stream.Failure -> raise (Stream.Error "Bad character literal.")
        in
        begin match Stream.peek strm__ with
          Some '\'' -> Stream.junk strm__; Some (Char c)
        | _ -> raise (Stream.Error "Single quote expected.")
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
    | _ -> Some (ident_or_keyword (get_string ()) true)
  and ident2 (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some
        ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' |
         '>' | '?' | '@' | '\\' | '~' | '^' | '|' | '*' as c) ->
        Stream.junk strm__; let s = strm__ in store c; ident2 s
    | _ -> Some (ident_or_keyword (get_string ()) false)
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
    | _ -> Some (Int (big_int_of_string (get_string ())))
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
            Stream.Failure -> raise (Stream.Error "Bad string literal.")
        in
        let s = strm__ in store c; string s
    | Some c -> Stream.junk strm__; let s = strm__ in store c; string s
    | _ -> raise Stream.Failure
  and char (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\\' ->
        Stream.junk strm__;
        begin try escape strm__ with
          Stream.Failure -> raise (Stream.Error "Bad character literal.")
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
            | _ -> raise (Stream.Error "Bad escape sequence.")
            end
        | _ -> raise (Stream.Error "Bad escape sequence.")
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
    | Some '\010' -> (Stream.junk strm__; new_loc_line strm__; multiline_comment strm__)
    | Some '\013' ->
      (Stream.junk strm__;
       (match Stream.peek strm__ with
        | Some '\010' -> Stream.junk strm__
        | _ -> ());
       new_loc_line strm__;
       multiline_comment strm__
      )
    | _ -> (Stream.junk strm__; multiline_comment strm__)
  in
  (current_loc,
   Stream.from (fun count ->
     (match next_token stream with
        Some t -> Some (current_loc(), t)
      | None -> None)))

let preprocess path loc stream streamSource =
  let path = ref path in
  let loc = ref loc in
  let stream = ref stream in
  let startOfLine = ref true in
  let stack: ((string * string) * (unit -> loc) * (loc * token) Stream.t * bool) list ref = ref [] in
  let defines: (string * (loc * token) list) list ref = ref [] in
  let push newPath =
    stack := (!path, !loc, !stream, !startOfLine)::!stack;
    path := newPath;
    let (newloc, newstream) = streamSource newPath in
    loc := newloc;
    stream := newstream;
    startOfLine := true
  in
  let define x toks =
    defines := (x, toks)::!defines
  in
  let peek() = Stream.peek (!stream) in
  let skip() =
    startOfLine := begin match peek() with Some (_, Eol) -> true | _ -> false end;
    if peek() <> None then Stream.junk (!stream)
  in
  let error msg = raise (ParseException (!loc(), msg)) in
  let next() =
    match peek() with
      Some t -> skip(); t
    | None -> error "Token expected"
  in
  let expect_eol() =
    match peek() with
      None -> ()
    | Some (_, Eol) -> ()
    | _ -> error "End of line expected."
  in
  let expect token =
    match next() with
      (_, t) when t = token -> ()
    | _ ->
      let txt = match token with Eol -> "end of line" | Kwd s -> "'" ^ s ^ "'" in
      error (txt ^ " expected")
  in
  let next_ident() =
    match next() with
      (_, Ident x) -> x
    | _ ->
      error "Identifier expected"
  in
  let rec skip_block() =
    if !startOfLine then
      match next() with
        (l, Kwd "#") ->
        begin
          match next() with
            (_, Kwd "endif") ->
            expect_eol();
            ()
          | (_, Kwd "ifndef") ->
            skip_block();
            skip_block()
          | _ -> skip_block()
        end
      | _ -> skip_block()
    else
    begin
      ignore (next());
      skip_block()
    end
  in
  let rec next_token() =
    let pop() =
      match !stack with
        [] -> None
      | (path0, loc0, stream0, startOfLine0)::stack0 ->
        path := path0;
        loc := loc0;
        stream := stream0;
        stack := stack0;
        startOfLine := startOfLine0;
        next_token()
    in
    if !startOfLine then
      match peek() with
        Some (l, Kwd "#") ->
        begin
          skip();
          match next() with
            (_, Kwd "include") ->
            begin
              match next() with
                (_, String includePath) ->
                expect_eol();
                begin
                  match includePath with
                    "bool.h" -> ()
				  | "assert.h" -> ()
                  | _ ->
                    let (basedir, relpath) = !path in
                    let resolvedRelPath = Filename.concat (Filename.dirname relpath) includePath in
                    push (basedir, resolvedRelPath)
                end;
                next_token()
              | _ ->
                error "String literal expected."
            end
          | (_, Kwd "define") ->
            let x = next_ident() in
            expect_eol();
            define x [];
            next_token()
          | (_, Kwd "ifndef") ->
            let x = next_ident() in
            expect_eol();
            if List.mem_assoc x !defines then
            begin
              skip_block();
              next_token()
            end
            else
              next_token()
          | (_, Kwd "endif") ->
            expect_eol();
            next_token()
          | (l, _) -> error "Expected one of: include, define, ifndef, endif."
        end
      | Some (_, Eol) -> skip(); next_token()
      | None -> pop()
      | t -> skip(); t
    else
      match peek() with
        (Some (l, Ident x)) as t ->
        skip();
        if List.mem_assoc x !defines then next_token() else t
      | Some (_, Eol) -> skip(); next_token()
      | None -> pop()
      | t -> skip(); t
  in
  Stream.from (fun count -> next_token())

type type_ =
    Bool
  | Void
  | IntType
  | RealType
  | Char
  | StringType
  | StructType of string
  | PtrType of type_
  | InductiveType of string (* type van inductive type *)
  | PredType of type_ list (* type van predicate -> lijst van types van args*)
  | ObjType of string (* voor java *)

type type_expr =
    StructTypeExpr of loc * string
  | PtrTypeExpr of loc * type_expr
  | ArrayTypeExpr of loc * type_expr
  | ManifestTypeExpr of loc * type_ (* primitive types? met regel-type*)
  | IdentTypeExpr of loc * string (*type van inductive type met regel-naam *)
  | PredTypeExpr of loc * type_expr list (* type def van predicate met regel-lijst van types van args *)

class fieldref (name: string) =
  object
    val mutable parent: string option = None
    val mutable range: type_ option = None
    method name = name
    method parent = match parent with None -> assert false | Some s -> s
    method range = match range with None -> assert false | Some r -> r
    method set_parent s = parent <- Some s
    method set_range r = range <- Some r
  end

(*class methodref (name: string) =
  object
    val mutable parent: string option = None
    val mutable args: list type_ option = None
    method name = name
    method parent = match parent with None -> assert false | Some s -> s
    method args = match args with None -> assert false | Some r -> r
    method set_parent s = parent <- Some s
    method set_args r = args <- Some r
  end*)
  
class predref (name: string) =
  object
    val mutable domain: type_ list option = None
    method name = name
    method domain = match domain with None -> assert false | Some d -> d
    method set_domain d = domain <- Some d
  end

type
  operator = Add | Sub | Le | Lt | Eq | Neq | And | Or | Not
and
  expr =
    True of loc
  | False of loc
  | Null of loc
  | Var of loc * string
  | Operation of loc * operator * expr list * type_ list option ref (* voor operaties met bovenstaande operators*)
  | IntLit of loc * big_int * type_ option ref (* int literal*)
  | StringLit of loc * string (* string literal *)
  | Read of loc * expr * fieldref (* lezen van een veld; hergebruiken voor java field acces *)
  | CallExpr of loc * string * pat list * pat list * func_binding(* oproep van functie/methode/lemma/fixpoint *)
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of loc * expr * switch_expr_clause list * type_ ref
  | PredNameExpr of loc * string (* naam van predicaat en line of code*)
  | FuncNameExpr of string (*function name *)
  | CastExpr of loc * type_expr * expr (* cast *)
  | SizeofExpr of loc * type_expr
and
  pat =
    LitPat of expr (* literal pattern *)
  | VarPat of string (* var pattern, aangeduid met ? in code *)
  | DummyPat (*dummy pattern, aangeduid met _ in code *)
and
  switch_expr_clause =
    SwitchExprClause of loc * string * string list * expr (* switch uitdrukking *)
and
  file_type_=
    Java
  | C
  | Header
and
  func_binding =
    Static
  | Instance
and
  visibility =
    Public
  | Protected
  | Private
and
  stmt =
    PureStmt of loc * stmt (* oproep van pure function in ghost range*)
  | Assign of loc * string * expr (* toekenning *)
  | DeclStmt of loc * type_expr * string * expr (* enkel declaratie *)
  | Write of loc * expr * fieldref * expr (*  overschrijven van huidige waarde*)
  | CallStmt of loc * string * expr list * func_binding(* oproep regel-naam-argumenten*)
  | IfStmt of loc * expr * stmt list * stmt list (* if  regel-conditie-branch1-branch2  *)
  | SwitchStmt of loc * expr * switch_stmt_clause list (* switch over inductief type regel-expr- constructor)*)
  | Assert of loc * pred (* assert regel-predicate *)
  | Open of loc * string * (loc * string) list * pat list * pat option (* open van predicate regel-pred fam-pred naam-pattern list- ...*)
  | Close of loc * string * (loc * string) list * pat list * pat option
  | ReturnStmt of loc * expr option (*return regel-return value (optie) *)
  | WhileStmt of loc * expr * pred * stmt list (* while regel-conditie-lus invariant- lus body *)
  | BlockStmt of loc * stmt list (* blok met {}   regel-body *)
and
  switch_stmt_clause =
  | SwitchStmtClause of loc * string * string list * stmt list (* clause die hoort bij switch statement over constructor*)
and
  pred =
    Access of loc * expr * fieldref * pat (*  toegang tot veld regel-expr-veld-pattern*)
  | CallPred of loc * predref * pat list * pat list (* predicate oproep regel-predicate referentie -args*)
  | ExprPred of loc * expr (*  uitdrukking regel-expr *)
  | Sep of loc * pred * pred (* seperate execution of &*& in de code regel-predicate 1 - predicate 2 *)
  | IfPred of loc * expr * pred * pred (* if-predicate in de vorm expr? p1:p2 regel-expr-p1-p2 *)
  | SwitchPred of loc * expr * switch_pred_clause list (* switch over cons van inductive type regel-expr-clauses*)
  | EmpPred of loc (* als "emp" bij requires/ensures staat -regel-*)
  | CoefPred of loc * pat * pred
and
  switch_pred_clause =
  | SwitchPredClause of loc * string * string list * pred (*  clauses bij switch  regel-cons-lijst v var in cons- body*)
and
  func_kind =
  | Regular
  | Fixpoint
  | Lemma
and
  spec =
    Contract of pred * pred (* contract van een functie requires predicate-ensures predicate *)
  | FuncTypeSpec of string
and
  meth =
  | Meth of loc * type_expr option * string * (type_expr * string) list * spec option * stmt list option * func_binding * visibility
and
  decl =
    Struct of loc * string * field list option
  | Inductive of loc * string * ctor list (* inductief data type regel-naam-lijst van constructors*)
  | Class of loc * string * meth list * field list (* java *)
  | PredFamilyDecl of loc * string * int * type_expr list 
  | PredFamilyInstanceDecl of loc * string * (loc * string) list * (type_expr * string) list * pred
  | Func of loc * func_kind * type_expr option * string * (type_expr * string) list * spec option * stmt list option * func_binding * visibility
  (* functie met regel-soort-return type-naam- lijst van parameters - contract - body*)
  | FuncTypeDecl of loc * type_expr option * string * (type_expr * string) list * (pred * pred)
  (* typedef met regel-return type-naam-parameter lijst - contract *)
and
  field =
  | Field of loc * type_expr * string * func_binding(* veld met regel-type-naam*)
and
  ctor =
  | Ctor of loc * string * type_expr list  (* constructor met regel-naam-lijst v types v args*)
 and
  member = FieldMember of field | MethMember of meth

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

let string_of_srcpos (p,l,c) = p ^ "(" ^ string_of_int l ^ "," ^ string_of_int c ^ ")"

let string_of_path (basedir, relpath) = Filename.concat basedir relpath

let string_of_loc ((p1, l1, c1), (p2, l2, c2)) =
  string_of_path p1 ^ "(" ^ string_of_int l1 ^ "," ^ string_of_int c1 ^
  if p1 = p2 then
    if l1 = l2 then
      if c1 = c2 then
        ""
      else
        "-" ^ string_of_int c2 ^ ")"
    else
      "-" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"
  else
    ")-" ^ string_of_path p2 ^ "(" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"
let string_of_func_kind f=
  match f with
    Lemma -> "lemma"
  | Regular -> "regular"
  | Fixpoint -> "fixpoint"
let tostring f=
  match f with
  Instance -> "instance"
  | Static -> "static"
let expr_loc e =
  match e with
    True l -> l
  | False l -> l
  | Null l -> l
  | Var (l, x) -> l
  | IntLit (l, n, t) -> l
  | StringLit (l, s) -> l
  | Operation (l, op, es, ts) -> l
  | Read (l, e, f) -> l
  | CallExpr (l, g, pats0, pats,_) -> l
  | IfExpr (l, e1, e2, e3) -> l
  | SwitchExpr (l, e, secs, _) -> l
  | SizeofExpr (l, t) -> l
  | PredNameExpr (l, g) -> l
  | CastExpr (l, te, e) -> l

let pred_loc p =
  match p with
    Access (l, e, f, rhs) -> l
  | CallPred (l, g, ies, es) -> l
  | ExprPred (l, e) -> l
  | Sep (l, p1, p2) -> l
  | IfPred (l, e, p1, p2) -> l
  | SwitchPred (l, e, spcs) -> l
  | EmpPred l -> l
  | CoefPred (l, coef, body) -> l
  
let stmt_loc s =
  match s with
    PureStmt (l, _) -> l
  | Assign (l, _, _) -> l
  | DeclStmt (l, _, _, _) -> l
  | Write (l, _, _, _) -> l
  | CallStmt (l,  _, _,_) -> l
  | IfStmt (l, _, _, _) -> l
  | SwitchStmt (l, _, _) -> l
  | Assert (l, _) -> l
  | Open (l, _, _, _, coef) -> l
  | Close (l, _, _, _, coef) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _) -> l
  | BlockStmt (l, ss) -> l

let type_expr_loc t =
  match t with
    ManifestTypeExpr (l, t) -> l
  | StructTypeExpr (l, sn) -> l
  | IdentTypeExpr (l, x) -> l
  | PtrTypeExpr (l, te) -> l
let veri_keywords= ["predicate";"requires";"|->"; "&*&"; "inductive";"fixpoint"; "switch"; "case"; ":";"return";
  "ensures";"close";"void"; "lemma";"open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; "<="; "&&";
  "||"; "forall"; "_"; "@*/"; "!";"predicate_family"; "predicate_family_instance";"assert"; "@"; "["; "]";"{";
  "}";";"; "int";"true"; "false";"("; ")"; ",";"="; "|";"+"; "-"; "=="; "?";
]
let c_keywords= ["struct";"*";"real";"uint"; "bool"; "char";"->";"sizeof";"typedef"; "#"; "include"; "ifndef";
  "define"; "endif";
]
let java_keywords= ["public" ;"class" ; "." ; "static" ; "string"; "boolean";"new";"null"(*;"this"*)
]
(*let lexer = make_lexer [
  "struct"; "{"; "}"; "*"; ";"; "int"; "real"; "uint"; "bool"; "char"; "true"; "false"; "predicate"; "("; ")"; ","; "requires";
  "->"; "|->"; "&*&"; "inductive"; "="; "|"; "fixpoint"; "switch"; "case"; ":";
  "return"; "+"; "-"; "=="; "?"; "ensures"; "sizeof"; "close"; "void"; "lemma";
  "open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; "<="; "&&"; "||"; "forall"; "_"; "@*/"; "!";
  "predicate_family"; "predicate_family_instance"; "typedef"; "#"; "include"; "ifndef"; "define"; "endif"; "assert"; "@"; "["; "]";
  "public" ;"class" ; "." ; "static" ; "string"; "boolean";"new";"null"
]
*)
let file_type path=
  begin
  if Filename.check_suffix (Filename.basename path) ".c" then C
  else if Filename.check_suffix (Filename.basename path) ".java" then Java
  else if Filename.check_suffix (Filename.basename path) ".h" then Header
  else failwith ("unknown extension")
  end
let opt p = parser [< v = p >] -> Some v | [< >] -> None
let rec comma_rep p = parser [< '(_, Kwd ","); v = p; vs = comma_rep p >] -> v::vs | [< >] -> []
let rep_comma p = parser [< v = p; vs = comma_rep p >] -> v::vs | [< >] -> []

let read_decls path stream streamSource reportKeyword reportGhostRange =
let lexer=
  match file_type path with
  Java -> make_lexer (veri_keywords@java_keywords)
  | _ -> make_lexer (veri_keywords@c_keywords)
in
begin
let tokenStreamSource path = lexer path (streamSource (string_of_path path)) reportKeyword in
let (loc, token_stream) = lexer (Filename.dirname path, Filename.basename path) stream reportKeyword in
let pp_token_stream = preprocess (Filename.dirname path, Filename.basename path) loc token_stream tokenStreamSource in
let rec parse_decls_eof = parser
  [< ds = parse_decls; _ = Stream.empty >] -> ds
and
  parse_decls = parser
  [< '((p1, _), Kwd "/*@"); ds = parse_pure_decls; '((_, p2), Kwd "@*/"); ds' = parse_decls >] -> let _ = reportGhostRange (p1, p2) in ds @ ds'
| [< '(l, Kwd "public");'(_, Kwd "class");'(_, Ident s);'(_, Kwd "{"); mem=parse_java_members s
    ;'(_, Kwd "}");ds=parse_decls>]->Class(l,s,methods mem,fields mem)::ds
| [< ds0 = parse_decl; ds = parse_decls >] -> ds0@ds
| [< >] -> []
and
  methods m=
  match m with
    MethMember (Meth (l, t, n, ps, co, ss,s,v))::ms -> Meth (l, t, n, ps, co, ss,s,v)::(methods ms)
    |_::ms -> methods ms
    | []->[]
and
  fields m=
  match m with
    FieldMember (Field (l, t, f,fb))::ms -> Field (l, t, f,fb)::(fields ms)
    |_::ms -> fields ms
    | []->[]
and
  parse_java_members cn= parser
  [<'(l, Kwd "public");m=parse_java_member l cn;mr=parse_java_members cn>] -> m::mr
| [<>] -> []
and
  parse_java_member l cn= parser
  [< '(_, Kwd "static");t=parse_return_type;'(_,Ident n);'(_, Kwd "(");
    ps = parse_paramlist;co = opt parse_spec; ss = parse_block>] -> MethMember(Meth(l,t,n,ps,co,Some ss,Static,Public))
| [< t=parse_type;'(_,Ident f);r=parser
       [<'(_, Kwd ";")>]->FieldMember(Field (l,t,f,Instance))
	   |[< '(_, Kwd "(");ps = parse_paramlist;co = opt parse_spec; ss = parse_block>]
	   -> let tp=match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t	in
	   MethMember(Meth(l,tp,f,(IdentTypeExpr(l,cn),"this")::ps,co,Some ss,Instance,Public))
	   >] -> r
and
  parse_decl = parser
  [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, Some fs)
  | [< '(_, Kwd ";") >] -> Struct (l, s, None)
  | [< t = parse_type_suffix (StructTypeExpr (l, s)); d = parse_func_rest Regular (Some t) >] -> d
  >] -> [d]
| [< '(l, Kwd "typedef"); rt = parse_return_type; '(_, Kwd "("); '(_, Kwd "*"); '(_, Ident g); '(_, Kwd ")"); '(_, Kwd "("); ps = parse_paramlist; '(_, Kwd ";"); c = parse_contract l >] ->
  [FuncTypeDecl (l, rt, g, ps, c)]
| [< t = parse_return_type; d = parse_func_rest Regular t >] -> [d]
and
  parse_pure_decls = parser
  [< ds0 = parse_pure_decl; ds = parse_pure_decls >] -> ds0 @ ds
| [< >] -> []
and
  parse_index_list = parser
  [< '(_, Kwd "("); is = rep_comma (parser [< '(l, Ident i) >] -> (l, i)); '(_, Kwd ")") >] -> is
and
  parse_pure_decl = parser
  [< '(l, Kwd "inductive"); '(_, Ident i); '(_, Kwd "="); cs = (parser [< cs = parse_ctors >] -> cs | [< cs = parse_ctors_suffix >] -> cs); '(_, Kwd ";") >] -> [Inductive (l, i, cs)]
| [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> [d]
| [< '(l, Kwd "predicate"); '(_, Ident g); '(_, Kwd "("); ps = parse_paramlist;
     body = (parser [< '(_, Kwd "requires"); p = parse_pred >] -> Some p | [< >] -> None); '(_, Kwd ";");
  >] -> [PredFamilyDecl (l, g, 0, List.map (fun (t, p) -> t) ps)] @ (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, [], ps, body)])
| [< '(l, Kwd "predicate_family"); '(_, Ident g); '(_, Kwd "("); is = parse_paramlist; '(_, Kwd "("); ps = parse_paramlist; '(_, Kwd ";") >]
  -> [PredFamilyDecl (l, g, List.length is, List.map (fun (t, p) -> t) ps)]
| [< '(l, Kwd "predicate_family_instance"); '(_, Ident g); is = parse_index_list; '(_, Kwd "("); ps = parse_paramlist;
     '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); >] -> [PredFamilyInstanceDecl (l, g, is, ps, p)]
| [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest Lemma t >] -> [d]
and
  parse_func_rest k t = parser
  [< '(l, Ident g); '(_, Kwd "("); ps = parse_paramlist; f =
    (parser
       [< '(_, Kwd ";"); co = opt parse_spec >] -> Func (l, k, t, g, ps, co, None,Static,Public)
     | [< co = opt parse_spec; ss = parse_block >] -> Func (l, k, t, g, ps, co, Some ss,Static,Public)
    ) >] -> f
and
  parse_ctors_suffix = parser
  [< '(_, Kwd "|"); cs = parse_ctors >] -> cs
| [< >] -> []
and parse_ctors = parser
  [< '(l, Ident cn); ts = (parser [< '(_, Kwd "("); ts = parse_types >] -> ts | [< >] -> []); cs = parse_ctors_suffix >] -> Ctor (l, cn, ts)::cs
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
  parse_java_fields = parser
  [<'(_, Kwd "public static")>] -> []
| [< '(_, Kwd "public");f = parse_field; fs = parse_java_fields >] -> f::fs
and
  parse_field = parser
  [< t = parse_type; '(l, Ident f); '(_, Kwd ";") >] -> Field (l, t, f,Instance)
and
  parse_return_type = parser
  [< t = parse_type >] -> match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t
and
  parse_type = parser
  [< t0 = parse_primary_type; t = parse_type_suffix t0 >] -> t
and
  parse_primary_type = parser
  [< '(l, Kwd "struct"); '(_, Ident s) >] -> StructTypeExpr (l, s)
| [< '(l, Kwd "int") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "string") >] -> ManifestTypeExpr (l, StringType)
| [< '(l, Kwd "real") >] -> ManifestTypeExpr (l, RealType)
| [< '(l, Kwd "uint") >] -> IdentTypeExpr (l, "uint")
| [< '(l, Kwd "bool") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "boolean") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "void") >] -> ManifestTypeExpr (l, Void)
| [< '(l, Kwd "char") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "predicate"); '(_, Kwd "("); ts = parse_types >] -> PredTypeExpr (l, ts)
| [< '(l, Ident n) >] -> IdentTypeExpr (l, n)
and
  parse_type_suffix t0 = parser
  [< '(l, Kwd "*"); t = parse_type_suffix (PtrTypeExpr (l, t0)) >] -> t
| [<'(l, Kwd "[");'(_, Kwd "]");>] -> ArrayTypeExpr(l,t0)
| [< >] -> t0
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
  parse_spec = parser
  [< '((sp1, _), Kwd "/*@"); spec = parser
      [< '(_, Kwd ":"); '(_, Ident fn); '(_, Kwd "@*/") >] -> FuncTypeSpec fn
    | [< '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); '((_, sp2), Kwd "@*/");
         '((sp3, _), Kwd "/*@"); '(_, Kwd "ensures"); q = parse_pred; '(_, Kwd ";"); '((_, sp4), Kwd "@*/")
         >] -> let _ = reportGhostRange (sp1, sp2); reportGhostRange (sp3, sp4) in Contract (p, q)
    >] -> spec
| [< '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "ensures"); q = parse_pred; '(_, Kwd ";") >] -> Contract (p, q)
and
  parse_contract l = parser
  [< spec = parse_spec >] -> match spec with Contract (p, q) -> (p, q) | FuncTypeSpec ftn -> raise (ParseException (l, "Function type specification not allowed here."))
and
  parse_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> ss
and
  parse_stmts = parser
  [< s = parse_stmt; ss = parse_stmts >] -> s::ss
| [< >] -> []
and
  parse_stmt = parser [< s = parse_stmt0 >] -> stats#stmtParsed; s
and
  parse_coef = parser
  [< '(l, Kwd "["); pat = parse_pattern; '(_, Kwd "]") >] -> pat
and
  parse_stmt0 = parser
  [< '((sp1, _), Kwd "/*@"); s = parse_stmt0; '((_, sp2), Kwd "@*/") >] -> let _ = reportGhostRange (sp1, sp2) in PureStmt ((sp1, sp2), s)
| [< '(l, Kwd "if"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); b1 = parse_block;
     s = parser
       [< '(_, Kwd "else"); b2 = parse_block >] -> IfStmt (l, e, b1, b2)
     | [< >] -> IfStmt (l, e, b1, [])
  >] -> s
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); sscs = parse_switch_stmt_clauses; '(_, Kwd "}") >] -> SwitchStmt (l, e, sscs)
| [< '(l, Kwd "assert"); p = parse_pred; '(_, Kwd ";") >] -> Assert (l, p)
| [< '(l, Kwd "open"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, es1, es2,_) -> Open (l, g, List.map (function (LitPat (Var (l, x))) -> (l, x) | e -> raise (ParseException (l, "Index expressions must be identifiers."))) es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [< '(l, Kwd "close"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, es1, es2,_) -> Close (l, g, List.map (function (LitPat (Var (l, x))) -> (l, x) | e -> raise (ParseException (l, "Index expressions must be identifiers."))) es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of close statement must be call expression.")))
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     '((sp1, _), Kwd "/*@"); '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '((_, sp2), Kwd "@*/");
     b = parse_block >] -> let _ = reportGhostRange (sp1, sp2) in WhileStmt (l, e, p, b)
| [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> BlockStmt (l, ss)
(*| [< '(l, Ident x); s= parser
    [<'(_, Kwd "->");'(_, Ident f);'(l, Kwd "=");rhs = parse_expr; '(_, Kwd ";")>]
       ->Write (l, Var (l, x), new fieldref f, rhs)
	| [<'(_, Kwd "=");e=parser
			[<rhs = parse_expr; '(_, Kwd ";")>]-> Assign (l, x, rhs)
			| [<'(_, Kwd "new");'(_, Ident y);'(_, Kwd "(");'(_, Kwd ")");'(_, Kwd ";")>] -> Assign(l,x,CallExpr(l,"new",[],[]))
			| [<'(_, Kwd ".");'(_, Ident f);args0 = parse_patlist;'(_, Kwd ";")>] -> Assign (l, x,CallExpr (l, x, [], args0))
			| [<'(_, Ident y);'(_, Kwd ".");'(_, Ident f);args0 = parse_patlist;'(_, Kwd ";")>] -> Assign (l, x,CallExpr (l, f, [], args0))
			>] -> e
   | [<'(_, Kwd ".");'(_, Ident f);e=parser
       [<'(l, Kwd "=");rhs = parse_expr; '(_, Kwd ";")>]->Write (l, Var (l, x), new fieldref f, rhs)
	   |[<>]->
	   | [<args0 = parse_patlist;'(_, Kwd ";")>] -> CallStmt (l, x, List.map (function LitPat x-> x) args0,Instance)
	   >] -> e
   | [< args0 = parse_patlist;'(_, Kwd ";")>] -> CallStmt (l, x, List.map (function LitPat x-> x) args0,Static)
   | [<'(_, Ident t);'(_, Kwd "=");e=parser
			[<rhs = parse_expr; '(_, Kwd ";")>] -> DeclStmt (l, IdentTypeExpr (l, x), t, rhs)
			| [<'(_, Kwd "new");'(_, Ident x);'(_, Kwd "(");'(_, Kwd ")");'(_, Kwd ";")>] -> Assign(l,t,CallExpr(l,"new",[],[]))>] -> e
  >] -> s *)
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] -> (match e with CallExpr (l, g, [], es,fb) -> CallStmt (l, g, List.map (function LitPat e -> e) es,fb) | _ -> raise (ParseException (expr_loc e, "An expression used as a statement must be a call expression.")))
  | [< '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] ->
    (match e with
     | Var (lx, x) -> Assign (l, x, rhs)
     | Read (_, e, f) -> Write (l, e, f, rhs)
     | _ -> raise (ParseException (expr_loc e, "The left-hand side of an assignment must be an identifier or a field dereference expression."))
    )
  | [<'(_, Ident x); '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >]->
    (match e with
     | Var (lx, t) -> DeclStmt (l, IdentTypeExpr (lx,t), x, rhs)
     | _ -> raise (ParseException (expr_loc e, "Parse error blabla."))
    )
  >] -> s
| [< te = parse_type; '(_, Ident x); '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, te, x, rhs)
and
  parse_switch_stmt_clauses = parser
  [< c = parse_switch_stmt_clause; cs = parse_switch_stmt_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_stmt_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); ss = parse_stmts >] -> SwitchStmtClause (l, c, pats, ss)
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
  parse_pred0 = parser
  [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_pred_clauses; '(_, Kwd "}") >] -> SwitchPred (l, e, cs)
| [< '(l, Kwd "emp") >] -> EmpPred l
| [< '(_, Kwd "("); p = parse_pred; '(_, Kwd ")") >] -> p
| [< '(l, Kwd "["); coef = parse_pattern; '(_, Kwd "]"); p = parse_pred0 >] -> CoefPred (l, coef, p)
| [< e = parse_conj_expr; p = parser
    [< '(l, Kwd "|->"); rhs = parse_pattern >] ->
    (match e with
     | Read (_, e, f) -> Access (l, e, f, rhs)
     | _ -> raise (ParseException (expr_loc e, "Left-hand side of access predicate must be a field dereference expression."))
    )
  | [< '(l, Kwd "?"); p1 = parse_pred; '(_, Kwd ":"); p2 = parse_pred >] -> IfPred (l, e, p1, p2)
  | [< >] ->
    (match e with
     | CallExpr (l, g, pats0, pats,_) -> CallPred (l, new predref g, pats0, pats)
     | _ -> ExprPred (expr_loc e, e)
    )
  >] -> p
and
  parse_pattern = parser
  [< '(_, Kwd "_") >] -> DummyPat
| [< '(_, Kwd "?"); '(lx, Ident x) >] -> VarPat x
| [< e = parse_expr >] -> LitPat e
and
  parse_switch_pred_clauses = parser
  [< c = parse_switch_pred_clause; cs = parse_switch_pred_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_pred_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); p = parse_pred; '(_, Kwd ";") >] -> SwitchPredClause (l, c, pats, p)
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
  [< '(l, Kwd "true") >] -> True l
| [< '(l, Kwd "false") >] -> False l
| [< '(l, Kwd "null") >] -> Null l
| [< '(l, Kwd "new");'(_, Ident x);'(_, Kwd "(");'(_, Kwd ")");>] -> CallExpr(l,"new",[],[],Static)
| [< '(l, Ident x); ex = parser
    [< args0 = parse_patlist; e = parser
      [< args = parse_patlist >] -> CallExpr (l, x, args0, args,Static)
    | [< >] -> CallExpr (l, x, [], args0,Static)
      >] -> e
	| [<'(l, Kwd ".");'(l, Ident f);e=parser
	    [<args0 = parse_patlist;>] -> CallExpr (l, f, [], LitPat(Var(l,x))::args0,Instance)
	   |[<>] -> Read (l, Var(l,x), new fieldref f)
	 >]->e
    | [< >] -> Var (l, x)
  >] -> ex
| [< '(l, Int i) >] -> IntLit (l, i, ref None)
| [< '(l, String s) >] -> StringLit (l, s)
| [< '(l, Kwd "(");
     e = parser
     [< e = parse_expr; '(_, Kwd ")") >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses; '(_, Kwd "}") >] -> SwitchExpr (l, e, cs, ref Void)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "!"); e = parse_expr_primary >] -> Operation(l, Not, [e], ref None)
| [< '(l, Kwd "@"); '(_, Ident g) >] -> PredNameExpr (l, g)
and
  parse_switch_expr_clauses = parser
  [< c = parse_switch_expr_clause; cs = parse_switch_expr_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_expr_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> SwitchExprClause (l, c, pats, e)
and
  parse_expr_suffix_rest e0 = parser
  [< '(l, Kwd "->"); '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, new fieldref f)) >] -> e
| [< '(l, Kwd "."); '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, new fieldref f)) >] ->e
| [< >] -> e0
and
  parse_expr_arith_rest e0 = parser
  [< '(l, Kwd "+"); e1 = parse_expr_suffix; e = parse_expr_arith_rest (Operation (l, Add, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "-"); e1 = parse_expr_suffix; e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_rel_rest e0 = parser
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Lt, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_conj_rest e0 = parser
  [< '(l, Kwd "&&"); e1 = parse_expr_rel; e = parse_expr_conj_rest (Operation (l, And, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "||"); e1 = parse_expr_rel; e = parse_expr_conj_rest (Operation (l, Or, [e0; e1], ref None)) >] -> e
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
    parse_decls_eof pp_token_stream
  with Stream.Error msg -> raise (ParseException (loc(), msg))
end

let flatmap f xs = List.concat (List.map f xs)
let rec drop n xs = if n = 0 then xs else drop (n - 1) (List.tl xs)
let rec list_make n x = if n = 0 then [] else x::list_make (n - 1) x

let rec try_assoc x xys =
  match xys with
    [] -> None
  | (x', y)::xys when x' = x -> Some y
  | _::xys -> try_assoc x xys

let rec try_assq x xys =
  match xys with
    [] -> None
  | (x', y)::xys when x' == x -> Some y
  | _::xys -> try_assq x xys

let try_assoc_i x xys =
  let rec iter k xys =
    match xys with
      [] -> None
    | (x', y)::xys when x' = x -> Some (k, y)
    | _::xys -> iter (k + 1) xys
  in
  iter 0 xys

let list_remove_dups xs =
  let rec iter ys xs =
    match xs with
      [] -> List.rev ys
    | x::xs -> if List.mem x ys then iter ys xs else iter (x::ys) xs
  in
  iter [] xs

let startswith s s0 =
  String.length s0 <= String.length s && String.sub s 0 (String.length s0) = s0

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

exception StaticError of loc * string

let static_error l msg = raise (StaticError (l, msg))

type 'termnode heap = ('termnode * 'termnode * 'termnode list * int option) list
type 'termnode env = (string * 'termnode) list
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext

let string_of_chunk (g, coef, ts, size) = "[" ^ coef ^ "]" ^ g ^ "(" ^ String.concat ", " ts ^ ")"

let string_of_heap h = String.concat " * " (List.map string_of_chunk h)

let string_of_context c =
  match c with
    Assuming t -> "Assuming " ^ t
  | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s
  | PushSubcontext -> "Entering subcontext"
  | PopSubcontext -> "Leaving subcontext"

exception SymbolicExecutionError of string context list * string * loc * string

let zip xs ys =
  let rec iter xs ys zs =
    match (xs, ys) with
      ([], []) -> Some (List.rev zs)
    | (x::xs, y::ys) -> iter xs ys ((x, y)::zs)
    | _ -> None
  in
  iter xs ys []

let do_finally tryBlock finallyBlock =
  let result =
    try
      tryBlock()
    with e -> finallyBlock(); raise e
  in
  finallyBlock();
  result

let verify_program_core (ctxt: ('typenode, 'symbol, 'termnode) Proverapi.context) verbose path stream streamSource reportKeyword reportGhostRange =

  let verbose_print_endline s = if verbose then print_endline s else () in
  let verbose_print_string s = if verbose then print_string s else () in

  let used_ids = ref [] in
  let used_ids_stack = ref ([]: string list list) in
  
  let push() =
    used_ids_stack := !used_ids::!used_ids_stack;
    ctxt#push
  in
  
  let pop() =
    let (ids::t) = !used_ids_stack in
    let _ = used_ids := ids in
    used_ids_stack := t;
    ctxt#pop
  in
  
  let in_temporary_context cont =
    push();
    cont();
    pop()
  in
  
  let mk_ident s =
    let rec iter k =
      let sk = s ^ string_of_int k in
      if List.mem sk !used_ids then iter (k + 1) else (used_ids := sk::!used_ids; sk)
    in
    let name = if List.mem s !used_ids then iter 0 else (used_ids := s::!used_ids; s) in
    name
  in
  
  let mk_symbol s domain range kind =
    ctxt#mk_symbol (mk_ident s) domain range kind
  in
  
  let alloc_nullary_ctor j s = mk_symbol s [] ctxt#type_inductive (Proverapi.Ctor j) in
  
  let imap f xs =
    let rec imapi i xs =
      match xs with
        [] -> []
      | x::xs -> f i x::imapi (i + 1) xs
    in
    imapi 0 xs
  in
  
  let myPath = Filename.dirname (Sys.argv.(0)) in
  let ds= 
    match file_type (Filename.basename path) with
	Java-> read_decls path stream streamSource reportKeyword reportGhostRange
	| _->
		let preludePath = Filename.concat myPath "prelude.h" in
		let preludeStreamSource path = Stream.of_string (readFile (Filename.concat myPath path)) in
		let ds0 = read_decls preludePath (Stream.of_string (readFile preludePath)) preludeStreamSource reportKeyword reportGhostRange in
		ds0 @ read_decls path stream streamSource reportKeyword reportGhostRange 
  in
  
  (* failwith "Done parsing."; *)
  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds_opt)::ds ->
        begin
          match try_assoc sn sdm with
            Some (_, Some _) -> static_error l "Duplicate struct name."
          | Some (_, None) | None -> iter ((sn, (l, fds_opt))::sdm) ds
        end
      | _::ds -> iter sdm ds
    in
    iter [] ds
  in
  
  let structmap =
    List.map
      (fun (sn, (l, fds_opt)) ->
         let rec iter fmap fds =
           match fds with
             [] -> (sn, (l, Some (List.rev fmap)))
           | Field (lf, t, f,Instance)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
                 | StructTypeExpr (lt, sn) ->
                   if List.mem_assoc sn structdeclmap then
                     StructType sn
                   else
                     static_error lt "No such struct."
                 | PtrTypeExpr (lt, te) -> PtrType (check_type te)
                 | _ -> static_error (type_expr_loc te) "Invalid field type or field type component."
               in
               iter ((f, (lf, check_type t))::fmap) fds
             )
         in
         begin
           match fds_opt with
             Some fds -> iter [] fds
           | None -> (sn, (l, None))
         end
      )
      structdeclmap
  in
  
  let dummy_srcpos = (("<nowhere>", "prelude"), 0, 0) in
  let dummy_loc = (dummy_srcpos, dummy_srcpos) in
  
  let inductivedeclmap =
    let rec iter idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, ctors))::ds ->
        if i = "bool" || i = "boolean" || i = "int" || List.mem_assoc i idm then
          static_error l "Duplicate datatype name."
        else
          iter ((i, (l, ctors))::idm) ds
      | _::ds -> iter idm ds
    in
    iter [("uint", (dummy_loc, []))] ds
  in
  
  let classdeclmap =
    let rec iter idm ds =
      match ds with
        [] -> idm
      | (Class (l, i, meths,fields))::ds ->
        if List.mem_assoc i idm then
          static_error l "Duplicate datatype name."
        else
          iter ((i, (l, meths,fields))::idm) ds
      | _::ds -> iter idm ds
    in
    iter [("Object", (dummy_loc,[],[]))] ds
  in
  
  let classfmap =
    List.map
      (fun (sn, (l,meths, fds_opt)) ->
         let rec iter fmap fds =
           match fds with
             [] -> (sn, (l,meths, Some (List.rev fmap)))
           | Field (lf, t, f,Instance)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
				 | IdentTypeExpr(lt, sn) -> 
				   if List.mem_assoc sn classdeclmap then
                     ObjType sn
                   else
                     static_error lt "No such struct."
                 | _ -> static_error (type_expr_loc te) "Invalid field type or field type component in class."
               in
               iter ((f, (lf, check_type t))::fmap) fds
             )
         in
          begin
           match fds_opt with
             fds -> iter [] fds
           | [] -> (sn, (l,meths,None))
         end
      )
      classdeclmap
  in
  let classmap =
    List.map
      (fun (sn, (l,meths_opt, fds)) ->
         let rec iter mmap meths =
           match meths with
             [] -> (sn, (l,Some (List.rev mmap),fds))
           | Meth (lm, t, n, ps, co, ss,fb,v)::meths ->
             if List.mem_assoc n mmap then
               static_error lm "Duplicate meth name."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
				 | ManifestTypeExpr (_, Bool) -> Bool
				 | IdentTypeExpr(lt, sn) -> 
				   if List.mem_assoc sn classdeclmap then
                     ObjType sn
                   else
                     static_error lt "No such struct."
                 | _ -> static_error (type_expr_loc te) "Invalid return type of this method."
               in
			   let check_t t=
			     match t with
				   Some ManifestTypeExpr (_, Void) -> None
				 | Some t-> Some (check_type t)
				 | None -> None
			   in
               iter ((n, (lm, check_t t,ps,co,ss,fb,v))::mmap) meths
             )
         in
          begin
           match meths_opt with
             meths -> iter [] meths
           | [] -> (sn, (l,None,fds))
         end
      )
      classfmap
  in
  
  let rec check_pure_type te =
    match te with
      ManifestTypeExpr (l, t) -> t
	| ArrayTypeExpr (l, t) -> check_pure_type t
    | IdentTypeExpr (l, id) ->
      if (List.mem_assoc id inductivedeclmap) then
	    InductiveType id
	  else
	    if (List.mem_assoc id classdeclmap) then 
		ObjType id
		else
        static_error l ("No such datatype."^id)
    | StructTypeExpr (l, sn) ->
      if not (List.mem_assoc sn structmap) then
        static_error l "No such struct."
      else
        StructType sn
    | PtrTypeExpr (l, te) -> PtrType (check_pure_type te)
    | PredTypeExpr (l, tes) -> PredType (List.map check_pure_type tes)
  in 
  
  let boolt = Bool in
  let intt = IntType in
  let uintt = InductiveType "uint" in
  
  let rec string_of_type t =
    match t with
      Bool -> "bool"
    | Void -> "void"
    | IntType -> "int"
    | RealType -> "real"
    | Char -> "char"
    | InductiveType i -> i
	| ObjType l -> l
    | StructType sn -> "struct " ^ sn
    | PtrType t -> string_of_type t ^ " *"
    | PredType ts -> "predicate(" ^ String.concat ", " (List.map string_of_type ts) ^ ")"
  in
  
  let typenode_of_type t =
    match t with
      Bool -> ctxt#type_bool
    | IntType -> ctxt#type_int
    | RealType -> ctxt#type_real
    | Char -> ctxt#type_int
	| StringType -> ctxt#type_int
    | InductiveType i -> ctxt#type_inductive
    | StructType sn -> assert false
	| ObjType n -> ctxt#type_int
    | PtrType t -> ctxt#type_int
    | PredType t -> ctxt#type_inductive
  in
  
  let functypenames = flatmap (function (FuncTypeDecl (_, _, g, _, _)) -> [g] | _ -> []) ds in
  let isfuncs =
    List.map (fun ftn ->
      let isfuncname = "is_" ^ ftn in
      let domain = [ctxt#type_int] in
      let symb = mk_symbol isfuncname domain ctxt#type_bool Uninterp in
      (isfuncname, (dummy_loc, Bool, [PtrType Void], symb))
    ) functypenames
  in
  
  let rec expect_type l t t0 =
    match (t, t0) with
      (PtrType _, PtrType Void) -> ()
	| (ObjType "null", ObjType _) -> ()
    | (PtrType Void, PtrType _) -> ()
    | (Char, IntType) -> ()
    | (PredType ts, PredType ts0) ->
      begin
        match zip ts ts0 with
          None -> static_error l ("Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
        | Some tpairs ->
          List.iter (fun (t, t0) -> expect_type l t t0) tpairs
      end
    | _ -> if t = t0 then () else static_error l ("Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
  in
  (* opstellen van inductivemap en purefuncmap *)
  let (inductivemap, purefuncmap) =
    let rec iter imap pfm ds =
      match ds with
        [] -> (List.rev imap, List.rev pfm)
      | Inductive (l, i, ctors)::ds ->
        let rec citer j ctormap pfm ctors =
          match ctors with
            [] -> iter ((i, (l, List.rev ctormap))::imap) pfm ds
          | Ctor (lc, cn, tes)::ctors ->
            if List.mem_assoc cn pfm then
              static_error lc "Duplicate pure function name."
            else (
              let ts = List.map check_pure_type tes in
              let csym =
                if ts = [] then
                  alloc_nullary_ctor j cn
                else
                  mk_symbol cn (List.map typenode_of_type ts) ctxt#type_inductive (Proverapi.Ctor j)
              in
              citer (j + 1) ((cn, (lc, ts))::ctormap) ((cn, (lc, InductiveType i, ts, csym))::pfm) ctors
            )
        in
        citer 0 [] pfm ctors
      | Func (l, Fixpoint, rto, g, ps, contract, body_opt,Static,Public)::ds ->
        let _ =
          if List.mem_assoc g pfm then static_error l "Duplicate pure function name."
        in
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void."
          | Some rt -> (check_pure_type rt)
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
            | (te, p)::ps ->
              let _ = if List.mem_assoc p pmap then static_error l "Duplicate parameter name." in
              let t = check_pure_type te in
              iter ((p, t)::pmap) ps
          in
          iter [] ps
        in
        let (index, ctorcount) = 
          match body_opt with
            Some [SwitchStmt (ls, e, cs)] -> (
            let ctorcount = List.length cs in
            match e with
              Var (l, x) -> (
              match try_assoc_i x pmap with
                None -> static_error l "Fixpoint function must switch on a parameter."
              | Some (index, InductiveType i) -> (
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
                      in (index, ctorcount)
                    | SwitchStmtClause (lc, cn, xs, body)::cs -> (
                      match try_assoc cn ctormap with
                        None -> static_error lc "No such constructor."
                      | Some (_, ts) ->
                        let xmap =
                          let rec iter xmap ts xs =
                            match (ts, xs) with
                              ([], []) -> xmap
                            | (t::ts, x::xs) ->
                              if List.mem_assoc x pmap then static_error lc "Pattern variable hides parameter.";
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
                        let rec check_ tenv e =
                          let check e = check_ tenv e in
                          let checkt e = checkt_ tenv e in
                          let promote_numeric e1 e2 ts =
                            let t1 = check e1 in
                            let t2 = check e2 in
                            match (t1, t2) with
                              (IntType, RealType) -> checkt e1 RealType; ts := Some [RealType; RealType]; RealType
                            | (t1, t2) -> checkt e2 t1; ts := Some [t1; t1]; t1
                          in
                          let promote l e1 e2 ts =
                            match promote_numeric e1 e2 ts with
                              (IntType | RealType) as t -> t
                            | _ -> static_error l "Expression of type int or real expected."
                          in
                          match e with
                            True l -> boolt
                          | False l -> boolt
                          | Var (l, x) -> (
                            match try_assoc x tenv with
                              None -> (
                                match try_assoc x pfm with
                                  Some (_, t, [], _) -> t
                                | _ -> static_error l "No such variable or constructor."
                              )
                            | Some t -> t
                            )
                          | Operation (l, (Eq | Neq), [e1; e2], ts) ->
                            ignore (promote_numeric e1 e2 ts);
                            boolt
                          | Operation (l, (Or | And), [e1; e2], ts) ->
                            let _ = checkt e1 boolt in
                            let _ = checkt e2 boolt in
                            boolt
                          | Operation (l, Not, [e], ts) ->
                            let _ = checkt e boolt in
                            boolt
                          | Operation (l, (Le | Lt), [e1; e2], ts) ->
                            ignore (promote l e1 e2 ts);
                            boolt
                          | Operation (l, (Add | Sub), [e1; e2], ts) ->
                            promote l e1 e2 ts
                          | IntLit (l, n, t) -> t := Some intt; intt
                          | StringLit (l, s) -> PtrType Char
                          | CallExpr (l, g', [], pats,_) -> (
                            match try_assoc g' pfm with
                              Some (l, t, ts, _) -> (
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
                                static_error l ("No such pure function: " ^ g')
                            )
                          | IfExpr (l, e1, e2, e3) ->
                            let _ = checkt e1 boolt in
                            let t = check e2 in
                            let _ = checkt e3 t in
                            t
                          | SwitchExpr (l, e, cs, tref) ->
                            let t = check e in
                            begin
                              match t with
                                InductiveType i ->
                                begin
                                  let (_, ctormap) = List.assoc i imap in
                                  let rec iter t0 ctors cs =
                                    match cs with
                                      [] ->
                                      if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors));
                                      begin
                                        match t0 with
                                          None -> static_error l "Switch expressions with zero cases are not yet supported."
                                        | Some t0 -> tref := t0; t0
                                      end
                                    | SwitchExprClause (lc, cn, xs, e)::cs ->
                                      begin
                                        match try_assoc cn ctormap with
                                          None -> static_error lc ("Not a constructor of inductive type '" ^ i ^ "'.")
                                        | Some (_, ts) ->
                                          if not (List.mem_assoc cn ctors) then static_error lc "Duplicate clause.";
                                          let xenv =
                                            let rec iter2 ts xs xenv =
                                              match (ts, xs) with
                                                ([], []) -> List.rev xenv
                                              | (t::ts, []) -> static_error lc "Too few pattern variables."
                                              | ([], _) -> static_error lc "Too many pattern variables."
                                              | (t::ts, x::xs) ->
                                                if List.mem_assoc x xenv then static_error lc "Duplicate pattern variable.";
                                                iter2 ts xs ((x, t)::xenv)
                                            in
                                            iter2 ts xs []
                                          in
                                          let t = check_ (xenv@tenv) e in
                                          let t0 =
                                            match t0 with
                                              None -> Some t
                                            | Some t0 -> expect_type (expr_loc e) t t0; Some t0
                                          in
                                          iter t0 (List.filter (fun (ctorname, _) -> ctorname <> cn) ctors) cs
                                      end
                                  in
                                  iter None ctormap cs
                                end
                            end
                          | e -> static_error (expr_loc e) "Expression form not allowed in fixpoint function body."
                        and checkt_ tenv e t0 =
                          match (e, t0) with
                            (IntLit (l, n, t), PtrType _) when eq_big_int n zero_big_int -> t:=Some IntType
                          | (IntLit (l, n, t), RealType) -> t:=Some RealType
                          | _ ->
                            let t = check_ tenv e in
                            if t = t0 then () else static_error (expr_loc e) ("Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
                        in
                        let _ = checkt_ tenv body rt in
                        iter (List.remove_assoc cn ctormap) cs
                      )
                  in
                  iter ctormap cs
                )
              | _ -> static_error l "Switch operand is not an inductive value."
              )
            )
          | _ -> static_error l "Body of fixpoint function must be switch statement."
        in
        let fsym = mk_symbol g (List.map (fun (p, t) -> typenode_of_type t) pmap) (typenode_of_type rt) (Proverapi.Fixpoint index) in
        iter imap ((g, (l, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ds
      | _::ds -> iter imap pfm ds
    in
    let indtypemap0 = [("uint", (dummy_loc, [("zero", (dummy_loc, [])); ("succ", (dummy_loc, [uintt]))]))] in
    let purefuncmap0 = 
      [("zero", (dummy_loc, uintt, [], alloc_nullary_ctor 0 "zero"));
       ("succ", (dummy_loc, uintt, [uintt], mk_symbol "succ" [ctxt#type_inductive] ctxt#type_inductive (Proverapi.Ctor 1)))]
    in
    let purefuncmap0 = purefuncmap0 @ isfuncs in
    iter indtypemap0 purefuncmap0 ds
  in
  
  let get_unique_var_symb x t = ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) [] in
  
  let mk_predfam p l arity ts = (p, (l, arity, ts, get_unique_var_symb p (PredType ts))) in
  
  let malloc_block_pred_map = 
    match file_type path with
	Java-> flatmap (function (sn, (_,_,_)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) dummy_loc 0 [ObjType sn])] 
	        | _ -> []) classmap
	| _ -> flatmap (function (sn, (_, Some _)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) dummy_loc 0 
	        [PtrType (StructType sn)])] | _ -> []) structmap 
	in

  let field_pred_map =
    match file_type path with
	Java-> flatmap
      (fun (sn, (_,_, fds_opt)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (_, t)) ->
              ((sn, fn), mk_predfam (sn ^ "_" ^ fn) dummy_loc 0 [ObjType sn; t])
             )
             fds
      )
      classmap
	| _ ->
    flatmap
      (fun (sn, (_, fds_opt)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (_, t)) ->
              ((sn, fn), mk_predfam (sn ^ "_" ^ fn) dummy_loc 0 [PtrType (StructType sn); t])
             )
             fds
      )
      structmap
  in
  
  
  let predfammap = 
    let rec iter pm ds =
      match ds with
        PredFamilyDecl (l, p, arity, tes)::ds ->
        let ts = List.map check_pure_type tes in
        begin
          match try_assoc p pm with
            Some (l0, arity0, ts0, symb0) ->
            if arity <> arity0 || ts <> ts0 then static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.");
            iter pm ds
          | None ->
            iter (mk_predfam p l arity ts::pm) ds
        end
      | _::ds -> iter pm ds
      | [] -> List.rev pm
    in
    let structpreds = List.map (fun (_, p) -> p) malloc_block_pred_map @ List.map (fun (_, p) -> p) field_pred_map in
    iter structpreds ds
  in
  
  let funcnames = 
    match file_type path with
	Java -> let rec mnames meths=
	  match meths with
	  Meth(l,rt,g,ps,c,b,fb,v)::rest -> g::mnames rest
	  | []->[]
	in
    list_remove_dups (flatmap (function (Class (l,cn,meths,fds)) -> mnames meths | _ -> []) ds )
	| _ -> list_remove_dups (flatmap (function (Func (l, Regular, rt, g, ps, c, b,Static,Public)) -> [g] | _ -> []) ds) 
  in
  
  let check_funcnamelist is =
    match file_type path with
    Java->List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such regular function name."; i) is
	| _ -> List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such regular function name."; i) is 
  in
  
  let predinstmap = 
    let rec iter pm ds =
      match ds with
        PredFamilyInstanceDecl (l, p, is, xs, body)::ds ->
        let (arity, ps) =
          match try_assoc p predfammap with
            None -> static_error l "No such predicate family."
          | Some (_, arity, ps, _) -> (arity, ps)
        in
        if List.length is <> arity then static_error l "Incorrect number of indexes.";
        let pxs =
          match zip ps xs with
            None -> static_error l "Incorrect number of parameters."
          | Some pxs -> pxs
        in
        let fns = check_funcnamelist is in
        let pfns = (p, fns) in
        let _ = if List.mem_assoc pfns pm then static_error l "Duplicate predicate family instance." in
        let rec iter2 xm pxs =
          match pxs with
            [] -> iter ((pfns, (l, List.rev xm, body))::pm) ds
          | (t0, (te, x))::xs ->
            let t = check_pure_type te in
            if t <> t0 then static_error (type_expr_loc te) "Predicate family instance parameter type does not match predicate family parameter type.";
            if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
            iter2 ((x, t)::xm) xs
        in
        iter2 [] pxs
      | _::ds -> iter pm ds
      | [] -> List.rev pm
    in  (* TODO: Include field_xxx predicate bodies in terms of 'range' predicates, so that a field can be turned into a range by opening it. *)
    iter [] ds
  in

  let rec check_expr tenv e =
    let check e = check_expr tenv e in
    let checkt e t0 = check_expr_t tenv e t0 in
    let promote_numeric e1 e2 ts =
      let t1 = check e1 in
      let t2 = check e2 in
      match (t1, t2) with
        (IntType, RealType) -> checkt e1 RealType; ts := Some [RealType; RealType]; RealType
      | (t1, t2) -> checkt e2 t1; ts := Some [t1; t1]; t1
    in
    let promote l e1 e2 ts =
      match promote_numeric e1 e2 ts with
        (IntType | RealType | PtrType _) as t -> t
      | _ -> static_error l "Expression of type int, real, or pointer type expected."
    in
    match e with
      True l -> boolt
    | False l -> boolt
	| Null l -> ObjType "null"
    | Var (l, x) ->
      begin
      match try_assoc x tenv with
        None ->
        begin
          match try_assoc x purefuncmap with
            Some (_, t, [], _) -> t
          | _ ->
            begin
              if List.mem x funcnames then
                match file_type path with
				Java -> static_error l "In java methods can't be used as pointers"
				| _ -> PtrType Void
              else
                begin
                  match try_assoc x predfammap with
                    Some (_, arity, ts, _) ->
                    if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
                    PredType ts
                  | None ->
                    static_error l "No such variable, constructor, regular function, or predicate."
                end
            end
        end
      | Some t -> t
      end
    | PredNameExpr (l, g) ->
      begin
        match try_assoc g predfammap with
          Some (_, arity, ts, _) ->
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
          PredType ts
        | None -> static_error l "No such predicate."
      end
    | Operation (l, (Eq | Neq), [e1; e2], ts) -> 
      ignore (promote_numeric e1 e2 ts);
      boolt
    | Operation (l, (Or | And), [e1; e2], ts) -> 
      let _ = checkt e1 boolt in
      let _ = checkt e2 boolt in
      boolt
    | Operation (l, Not, [e], ts) -> 
      let _ = checkt e boolt in
      boolt
    | Operation (l, (Le | Lt), [e1; e2], ts) -> 
      ignore (promote l e1 e2 ts);
      boolt
    | Operation (l, (Add | Sub), [e1; e2], ts) ->
      let t1 = check e1 in
      begin
        match t1 with
          PtrType Char | PtrType Void -> checkt e2 intt; ts:=Some [t1; IntType]; t1
        | IntType | RealType -> promote l e1 e2 ts
      end
    | IntLit (l, n, t) -> t := Some intt; intt 
    | StringLit (l, s) -> PtrType Char
    | CastExpr (l, te, e) ->
      let t = check_pure_type te in
      begin
        match (e, t) with
          (IntLit (_, n, tp), PtrType _) -> tp := Some t
        | _ -> checkt e t
      end;
      t
    | Read (l, e, f) -> check_deref l tenv e f
    | CallExpr (l, g', [], pats,_) -> (
      match try_assoc g' purefuncmap with
        Some (l, t, ts, _) -> (
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
      | None -> static_error l "No such pure function."
      )
    | IfExpr (l, e1, e2, e3) ->
      let _ = checkt e1 boolt in
      let t = check e2 in
      let _ = checkt e3 t in
      t
    | FuncNameExpr _ -> PtrType Void
    | SwitchExpr (l, e, cs, tref) ->
      let t = check e in
      begin
        match t with
          InductiveType i ->
          begin
            let (_, ctormap) = List.assoc i inductivemap in
            let rec iter t0 ctors cs =
              match cs with
                [] ->
                if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors));
                begin
                  match t0 with
                    None -> static_error l "Switch expressions with zero clauses are not yet supported."
                  | Some t0 -> tref := t0; t0
                end
              | SwitchExprClause (lc, cn, xs, e)::cs ->
                begin
                  match try_assoc cn ctormap with
                    None ->
                    static_error lc ("Not a constructor of inductive type '" ^ i ^ "'.")
                  | Some (_, ts) ->
                    if not (List.mem_assoc cn ctors) then static_error lc "Duplicate clause.";
                    let xenv =
                      let rec iter2 ts xs xenv =
                        match (ts, xs) with
                          ([], []) -> List.rev xenv
                        | (t::ts, []) -> static_error lc "Too few pattern variables."
                        | ([], _) -> static_error lc "Too many pattern variables."
                        | (t::ts, x::xs) ->
                          if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
                          if List.mem_assoc x xenv then static_error lc "Duplicate pattern variable.";
                          iter2 ts xs ((x, t)::xenv)
                      in
                      iter2 ts xs []
                    in
                    let t = check_expr (xenv@tenv) e in
                    let t0 =
                      match t0 with
                        None -> Some t
                      | Some t0 -> expect_type (expr_loc e) t t0; Some t0
                    in
                    iter t0 (List.filter (fun (ctorname, _) -> ctorname <> cn) ctors) cs
                end
            in
            iter None ctormap cs
          end
        | _ -> static_error l "Switch expression operand must be inductive value."
      end
    | e -> static_error (expr_loc e) "Expression form not allowed here."
  and check_expr_t tenv e t0 =
    match (e, t0) with
      (IntLit (l, n, t), PtrType _) when eq_big_int n zero_big_int -> t:=Some IntType
    | (IntLit (l, n, t), RealType) -> t:=Some RealType
    | (IntLit (l, n, t), Char) ->
      if not (le_big_int zero_big_int n && le_big_int n (big_int_of_int 127)) then
        static_error l "Integer literal used as char must be between 0 and 127.";
      t:=Some IntType
    | _ ->
      let t = check_expr tenv e in expect_type (expr_loc e) t t0
  and check_deref l tenv e f =
    let t = check_expr tenv e in
    begin
    match t with
    | PtrType (StructType sn) ->
      begin
      match List.assoc sn structmap with
        (_, Some fds) ->
        begin
          match try_assoc f#name fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.")
          | Some (_, t) -> f#set_parent sn; f#set_range t; t
        end
      | (_, None) -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' was declared without a body.")
      end
	| ObjType sn ->
	  begin
      match List.assoc sn classmap with
        (_,_, Some fds) ->
        begin
          match try_assoc f#name fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.")
          | Some (_, t) -> f#set_parent sn; f#set_range t; t
        end
      | (_,_,None) -> static_error l ("Invalid dereference; class '" ^ sn ^ "' was declared without a body.")
      end
    | _ -> static_error l "Target expression of field dereference should be of type pointer-to-struct."
    end
  in

  let check_pat l tenv t p =
    match p with
      LitPat e -> check_expr_t tenv e t; tenv
    | VarPat x ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
      (x, t)::tenv
    | DummyPat -> tenv
  in
  
  let rec check_pats l tenv ts ps =
    match (ts, ps) with
      ([], []) -> tenv
    | (t::ts, p::ps) ->
      check_pats l (check_pat l tenv t p) ts ps
    | ([], _) -> static_error l "Too many patterns"
    | (_, []) -> static_error l "Too few patterns"
  in

  let rec check_pred tenv p cont =
    match p with
      Access (l, e, f, v) ->
      let t = check_deref l tenv e f in
      let tenv' = check_pat l tenv t v in
      cont tenv'
    | CallPred (l, p, ps0, ps) ->
      let (arity, xs) =
        match try_assoc p#name predfammap with
          Some (_, arity, xs, _) -> (arity, xs)
        | None ->
          begin
            match try_assoc p#name tenv with
              None -> static_error l "No such predicate."
            | Some (PredType ts) -> (0, ts)
            | Some _ -> static_error l "Variable is not of predicate type."
          end
      in
      begin
        if List.length ps0 <> arity then static_error l "Incorrect number of indexes.";
        let ts = list_make arity (PtrType Void) @ xs in
        begin
        match zip ts (ps0 @ ps) with
          None -> static_error l "Incorrect number of arguments."
        | Some bs ->
          let rec iter tenv bs =
            match bs with
              [] -> p#set_domain ts; cont tenv
            | (t, p)::bs ->
              let tenv = check_pat l tenv t p in iter tenv bs
          in
          iter tenv bs
        end
      end
    | ExprPred (l, e) ->
      check_expr_t tenv e boolt; cont tenv
    | Sep (l, p1, p2) ->
      check_pred tenv p1 (fun tenv -> check_pred tenv p2 cont)
    | IfPred (l, e, p1, p2) ->
      check_expr_t tenv e boolt;
      check_pred tenv p1 (fun _ -> ());
      check_pred tenv p2 (fun _ -> ());
      cont tenv
    | SwitchPred (l, e, cs) ->
      let t = check_expr tenv e in
      begin
      match t with
      | InductiveType i ->
        begin
        match try_assoc i inductivemap with
          None -> static_error l "Switch operand is not an inductive value."
        | Some (l, ctormap) ->
          let rec iter ctormap cs =
            match cs with
              [] ->
              let _ = 
                match ctormap with
                  [] -> ()
                | (cn, _)::_ ->
                  static_error l ("Missing case: '" ^ cn ^ "'.")
              in cont tenv
            | SwitchPredClause (lc, cn, xs, body)::cs ->
              begin
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor."
              | Some (_, ts) ->
                let xmap =
                  let rec iter xmap ts xs =
                    match (ts, xs) with
                      ([], []) -> xmap
                    | (t::ts, x::xs) ->
                      if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
                      let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." in
                      iter ((x, t)::xmap) ts xs
                    | ([], _) -> static_error lc "Too many pattern variables."
                    | _ -> static_error lc "Too few pattern variables."
                  in
                  iter [] ts xs
                in
                let tenv = xmap @ tenv in
                (check_pred tenv body (fun _ -> ());
                iter (List.remove_assoc cn ctormap) cs)
              end
          in
          iter ctormap cs
        end
      | _ -> static_error l "Switch operand is not an inductive value."
      end
    | EmpPred l -> cont tenv
    | CoefPred (l, coef, body) ->
      let tenv = check_pat l tenv RealType coef in
      check_pred tenv body cont
  in

  let _ =
    List.iter
      (
        function
          (pfns, (l, xs, body)) -> check_pred xs body (fun _ -> ())
        | _ -> ()
      )
      predinstmap
  in

  let check_ghost ghostenv l e =
    let rec iter e =
      match e with
        Var (l, x) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context."
      | Operation (l, _, es, _) -> List.iter iter es
      | CallExpr (l, _, [], pats,_) -> List.iter (function LitPat e -> iter e | _ -> ()) pats
      | IfExpr (l, e1, e2, e3) -> (iter e1; iter e2; iter e3)
      | _ -> ()
    in
    iter e
  in

  let funcnameterms = 
    match file_type path with
	Java ->[] (* in java methods can't be used as pointers *)
	| _ -> List.map (fun fn -> (fn, get_unique_var_symb fn (PtrType Void))) funcnames
  in
  
  let real_unit = ctxt#mk_reallit 1 in
  
  let min_int_big_int = big_int_of_string "-2147483648" in
  let min_int_term = ctxt#mk_intlit_of_string "-2147483648" in
  let max_int_big_int = big_int_of_string "2147483647" in
  let max_int_term = ctxt#mk_intlit_of_string "2147483647" in
  let max_ptr_big_int = big_int_of_string "4294967295" in
  let max_ptr_term = ctxt#mk_intlit_of_string "4294967295" in
  
  let rec eval_core assert_term read_field (env: (string * 'termnode) list) e : 'termnode =
    let ev = eval_core assert_term read_field env in
    let check_overflow l min t max =
      begin
      match assert_term with
        None -> ()
      | Some assert_term ->
        assert_term l (ctxt#mk_le min t) "Potential arithmetic underflow.";
        assert_term l (ctxt#mk_le t max) "Potential arithmetic overflow."
      end;
      t
    in
    match e with
      True l -> ctxt#mk_true
    | False l -> ctxt#mk_false
	| Null l -> ctxt#mk_intlit 0
    | Var (l, x) ->
      begin (* Note: this lookup sequence must match exactly the one in check_expr *)
        match try_assoc x env with
          None ->
          begin
            match try_assoc x purefuncmap with
              Some (lg, t, [], s) -> ctxt#mk_app s []
            | _ ->
              begin
                match try_assoc x funcnameterms with
                  Some t -> t
                | None ->
                  begin
                    match try_assoc x predfammap with
                      Some (_, _, _, symb) -> symb
                    | None -> static_error l "No such variable, constructor, regular function, or predicate."
                  end
              end
          end
        | Some t -> t
      end
    | PredNameExpr (l, g) -> let (_, _, _, symb) = List.assoc g predfammap in symb
    | CastExpr (l, te, e) ->
      let t = check_pure_type te in
      begin
        match (e, t) with
          (IntLit (_, n, _), PtrType _) ->
          if assert_term <> None && not (le_big_int zero_big_int n && le_big_int n max_ptr_big_int) then static_error l "Int literal is out of range.";
          ctxt#mk_intlit_of_string (string_of_big_int n)
        | _ -> ev e
      end
    | IntLit (l, n, t) when !t = Some IntType ->
      if assert_term <> None && not (le_big_int min_int_big_int n && le_big_int n max_int_big_int) then static_error l "Int literal is out of range.";
      begin
        try
          let n = int_of_big_int n in ctxt#mk_intlit n
        with Failure "int_of_big_int" -> ctxt#mk_intlit_of_string (string_of_big_int n)
      end
    | IntLit (l, n, t) when !t = Some RealType ->
      if eq_big_int n unit_big_int then real_unit
      else if eq_big_int n zero_big_int then ctxt#mk_reallit 0
      else static_error l "Real number literals other than 0 and 1 are not yet supported."
    | StringLit (l, s) -> get_unique_var_symb "stringLiteral" (PtrType Char)
    | CallExpr (l, g, [], pats,_) ->
      begin
        match try_assoc g purefuncmap with
          None -> static_error l "No such pure function."
        | Some (lg, t, pts, s) -> ctxt#mk_app s (List.map (function (LitPat e) -> ev e) pats)
      end
    | Operation (l, And, [e1; e2], ts) -> ctxt#mk_and (ev e1) (ev e2)
    | Operation (l, Or, [e1; e2], ts) -> ctxt#mk_or (ev e1) (ev e2)
    | Operation (l, Not, [e], ts) -> ctxt#mk_not (ev e)
    | IfExpr (l, e1, e2, e3) -> ctxt#mk_ifthenelse (ev e1) (ev e2) (ev e3)
    | Operation (l, Eq, [e1; e2], ts) -> ctxt#mk_eq (ev e1) (ev e2)
    | Operation (l, Neq, [e1; e2], ts) -> ctxt#mk_not (ctxt#mk_eq (ev e1) (ev e2))
    | Operation (l, Add, [e1; e2], ts) ->
      begin
        match !ts with
          Some [IntType; IntType] ->
          check_overflow l min_int_term (ctxt#mk_add (ev e1) (ev e2)) max_int_term
        | Some [PtrType (Char|Void); IntType] ->
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_add (ev e1) (ev e2)) max_ptr_term
        | Some [RealType; RealType] ->
          ctxt#mk_real_add (ev e1) (ev e2)
        | _ -> static_error l "Internal error in eval."
      end
    | Operation (l, Sub, [e1; e2], ts) ->
      begin
        match !ts with
          Some [IntType; IntType] ->
          check_overflow l min_int_term (ctxt#mk_sub (ev e1) (ev e2)) max_int_term
        | Some [PtrType Char; IntType] ->
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_sub (ev e1) (ev e2)) max_ptr_term
        | Some [RealType; RealType] ->
          ctxt#mk_real_sub (ev e1) (ev e2)
      end
    | Operation (l, Le, [e1; e2], ts) -> (match !ts with Some ([IntType; IntType] | [PtrType _; PtrType _]) -> ctxt#mk_le (ev e1) (ev e2) | Some [RealType; RealType] -> ctxt#mk_real_le (ev e1) (ev e2))
    | Operation (l, Lt, [e1; e2], ts) -> (match !ts with Some ([IntType; IntType] | [PtrType _; PtrType _]) -> ctxt#mk_lt (ev e1) (ev e2) | Some [RealType; RealType] -> ctxt#mk_real_lt (ev e1) (ev e2))
    | Read(l, e, f) ->
      begin
        match read_field with
          None -> static_error l "Cannot use field dereference in this context."
        | Some read_field -> read_field l (ev e) f
      end
    | FuncNameExpr fn -> List.assoc fn funcnameterms
    | SwitchExpr (l, e, cs, tref) ->
      let g = mk_ident "switch_expression" in
      let t = ev e in
      let env =
        let rec iter env0 env =
          match env with
            [] -> env0
          | (x, t)::env ->
            if List.mem_assoc x env0 then iter env0 env else iter ((x, t)::env0) env
        in
        iter [] env
      in
      let tp = !tref in
      let symbol = ctxt#mk_symbol g (ctxt#get_type t :: List.map (fun (x, t) -> ctxt#get_type t) env) (typenode_of_type tp) (Proverapi.Fixpoint 0) in
      let fpclauses =
        List.map
          (function (SwitchExprClause (_, cn, ps, e)) ->
             let (_, pts, _, csym) = List.assoc cn purefuncmap in
             let apply gvs cvs =
               let Some genv = zip ("#value"::List.map (fun (x, t) -> x) env) gvs in
               let Some penv = zip ps cvs in
               let env = penv@genv in
               eval_core None None env e
             in
             (csym, apply)
          )
          cs
      in
      ctxt#set_fpclauses symbol 0 fpclauses;
      ctxt#mk_app symbol (t::List.map (fun (x, t) -> t) env)
    | _ -> static_error (expr_loc e) "Construct not supported in this position."
  in
  
  let eval = eval_core None in

  let _ =
    List.iter
    (function
     | Func (l, Fixpoint, t, g, ps, _, Some [SwitchStmt (_, Var (_, x), cs)],Static,Public) ->
       let rec index_of_param i x0 ps =
         match ps with
           [] -> assert false
         | (tp, x)::ps -> if x = x0 then i else index_of_param (i + 1) x0 ps
       in
       let i = index_of_param 0 x ps in
       let fsym = match List.assoc g purefuncmap with (l, rt, ts, s) -> s in
       let clauses =
         List.map
           (function (SwitchStmtClause (lc, cn, pats, [ReturnStmt (_, Some e)])) ->
              let ctorsym = match List.assoc cn purefuncmap with (l, rt, ts, s) -> s in
              let eval_body gts cts =
                let Some pts = zip ps gts in
                let penv = List.map (fun ((tp, p), t) -> (p, t)) pts in
                let Some patenv = zip pats cts in
                eval None (patenv @ penv) e
              in
              (ctorsym, eval_body)
           )
           cs
       in
       ctxt#set_fpclauses fsym i clauses
     | _ -> ()
    )
    ds
  in

  let contextStack = ref ([]: 'termnode context list) in
  
  let push_context msg = let _ = contextStack := msg::!contextStack in () in
  let pop_context () = let _ = let (h::t) = !contextStack in contextStack := t in () in
    
  let with_context msg cont =
    stats#execStep;
    push_context msg;
    cont();
    pop_context();
    ()
  in
  
  (* TODO: To improve performance, push only when branching, i.e. not at every assume. *)
  
  let assume t cont =
    push_context (Assuming t);
    ctxt#push;
    begin
      match ctxt#assume t with
        Unknown -> cont()
      | Unsat -> ()
    end;
    pop_context();
    ctxt#pop
  in
  
  let assume_eq t1 t2 cont = assume (ctxt#mk_eq t1 t2) cont in
  let assume_neq t1 t2 cont = assume (ctxt#mk_not (ctxt#mk_eq t1 t2)) cont in

  let pprint_context_stack cs =
    List.map
      (function
         Assuming t -> Assuming (ctxt#pprint t)
       | Executing (h, env, l, msg) ->
         let h' = List.map (fun (g, coef, ts, size) -> (ctxt#pprint g, ctxt#pprint coef, List.map (fun t -> ctxt#pprint t) ts, size)) h in
         let env' = List.map (fun (x, t) -> (x, ctxt#pprint t)) env in
         Executing (h', env', l, msg)
       | PushSubcontext -> PushSubcontext
       | PopSubcontext -> PopSubcontext)
      cs
  in

  let assert_term t h env l msg =
    if not (ctxt#query t) then
      raise (SymbolicExecutionError (pprint_context_stack !contextStack, ctxt#pprint t, l, msg))
  in

  let assert_false h env l msg =
    raise (SymbolicExecutionError (pprint_context_stack !contextStack, "false", l, msg))
  in
  
  let assert_expr env e h env l msg = assert_term (eval None env e) h env l msg in
  
  let success() = () in
  
  let branch cont1 cont2 =
    stats#branch;
    in_temporary_context (fun _ -> cont1());
    in_temporary_context (fun _ -> cont2())
  in
  
  let real_unit_pat = LitPat (IntLit (dummy_loc, unit_big_int, ref (Some RealType))) in
  
  let evalpat ghostenv env pat tp cont =
    if pat == real_unit_pat then cont ghostenv env real_unit else
    match pat with
      LitPat e -> cont ghostenv env (eval None env e)
    | VarPat x -> let t = get_unique_var_symb x tp in cont (x::ghostenv) (update env x t) t
    | DummyPat -> let t = get_unique_var_symb "dummy" tp in cont ghostenv env t
  in
  
  let rec evalpats ghostenv env pats tps cont =
    match (pats, tps) with
      ([], []) -> cont ghostenv env []
    | (pat::pats, tp::tps) -> evalpat ghostenv env pat tp (fun ghostenv env t -> evalpats ghostenv env pats tps (fun ghostenv env ts -> cont ghostenv env (t::ts)))
  in

  let real_mul l t1 t2 =
    if t1 == real_unit then t2 else if t2 == real_unit then t1 else static_error l "Real multiplication not yet supported."
  in
  
  let real_div l t1 t2 =
    if t2 == real_unit then t1 else static_error l "Real division not yet supported."
  in
  
  let assume_field h0 f tp tv tcoef cont =
    let (_, (_, _, _, symb)) = List.assoc (f#parent, f#name) field_pred_map in
    let rec iter h =
      match h with
        [] -> cont ((symb, tcoef, [tp; tv], None)::h0)
      | (g, tcoef', [tp'; _], _)::h when g == symb && tcoef' == real_unit -> assume_neq tp tp' (fun _ -> iter h)
      | _::h -> iter h
    in
    iter h0
  in
  
  let rec assume_pred h ghostenv (env: (string * 'termnode) list) p coef size_first size_all cont =
    with_context (Executing (h, env, pred_loc p, "Assuming predicate")) (fun _ ->
    let ev = eval None env in
    match p with
    | Access (l, e, f, rhs) ->
      let te = ev e in evalpat ghostenv env rhs f#range (fun ghostenv env t -> assume_field h f te t coef (fun h -> cont h ghostenv env))
    | CallPred (l, g, pats0, pats) ->
      let g_symb =
        match try_assoc g#name predfammap with
          Some (_, _, _, symb) -> symb
        | None -> List.assoc g#name env
      in
      evalpats ghostenv env (pats0 @ pats) g#domain (fun ghostenv env ts -> cont ((g_symb, coef, ts, size_first)::h) ghostenv env)
    | ExprPred (l, e) -> assume (ev e) (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) -> assume_pred h ghostenv env p1 coef size_first size_all (fun h ghostenv env -> assume_pred h ghostenv env p2 coef size_all size_all cont)
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ = cont h ghostenv env in
      branch (fun _ -> assume (ev e) (fun _ -> assume_pred h ghostenv env p1 coef size_all size_all cont)) (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> assume_pred h ghostenv env p2 coef size_all size_all cont))
    | SwitchPred (l, e, cs) ->
      let cont h _ _ = cont h ghostenv env in
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          branch
            (fun _ ->
               let (_, _, tps, cs) = List.assoc cn purefuncmap in
               let Some pts = zip pats tps in
               let xts = List.map (fun (x, tp) -> (x, get_unique_var_symb x tp)) pts in
               assume_eq t (ctxt#mk_app cs (List.map (fun (x, t) -> t) xts)) (fun _ -> assume_pred h (pats @ ghostenv) (xts @ env) p coef size_all size_all cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env
    | CoefPred (l, coef', body) ->
      evalpat ghostenv env coef' RealType (fun ghostenv env coef' -> assume_pred h ghostenv env body (real_mul l coef coef') size_first size_all cont)
    )
  in
  
  let definitely_equal t1 t2 =
    let result = t1 == t2 || ctxt#query (ctxt#mk_eq t1 t2) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  in
  
  let match_chunk ghostenv env l g coef coefpat pats (g', coef0, ts0, size0) =
    let match_pat ghostenv env pat t cont =
      match (pat, t) with
        (LitPat e, t) -> if definitely_equal (eval None env e) t then cont ghostenv env else None
      | (VarPat x, t) -> cont (x::ghostenv) (update env x t)
      | (DummyPat, t) -> cont ghostenv env
    in
    let rec iter ghostenv env pats ts =
      match (pats, ts) with
        (pat::pats, t::ts) -> match_pat ghostenv env pat t (fun ghostenv env -> iter ghostenv env pats ts)
      | ([], []) -> Some (coef0, ts0, size0, ghostenv, env)
    in
      if g == g' then
        begin
          if coef == real_unit && coefpat == real_unit_pat && coef0 == real_unit then iter ghostenv env pats ts0 else
          match coefpat with
            LitPat e -> if definitely_equal (real_mul l coef (eval None env e)) coef0 then iter ghostenv env pats ts0 else None
          | VarPat x -> iter (x::ghostenv) (update env x (real_div l coef0 coef)) pats ts0
          | DummyPat -> iter ghostenv env pats ts0
        end
      else
        None
  in
  
  let read_field h env l t f =
    let (_, (_, _, _, f_symb)) = List.assoc (f#parent, f#name) field_pred_map in
    let rec iter h =
      match h with
        [] -> assert_false h env l ("No matching heap chunk: " ^ ctxt#pprint f_symb)
      | (g, coef, [t0; v], _)::_ when g == f_symb && definitely_equal t0 t -> v
      | _::h -> iter h
    in
    iter h
  in

  let assert_chunk h ghostenv env l g coef coefpat pats cont =
    let rec iter hprefix h =
      match h with
        [] -> []
      | chunk::h ->
        let matches =
          match match_chunk ghostenv env l g coef coefpat pats chunk with
            None -> []
          | Some (coef, ts, size, ghostenv, env) -> [(hprefix @ h, coef, ts, size, ghostenv, env)]
        in
          matches @ iter (chunk::hprefix) h
    in
    match iter [] h with
      [] -> assert_false h env l ("No matching heap chunks: " ^ ctxt#pprint g)
(*      
    | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
    | _ -> assert_false h env l "Multiple matching heap chunks."
*)
    | (h, coef, ts, size, ghostenv, env)::_ -> cont h coef ts size ghostenv env
  in
  
  let rec assert_pred h ghostenv env p coef (cont: 'termnode heap -> string list -> 'termnode env -> int option -> unit) =
    with_context (Executing (h, env, pred_loc p, "Asserting predicate")) (fun _ ->
    let ev = eval None env in
    let access l coefpat e f rhs =
      let (_, (_, _, _, symb)) = List.assoc (f#parent, f#name) field_pred_map in
      assert_chunk h ghostenv env l symb coef coefpat [LitPat e; rhs] (fun h coef ts size ghostenv env -> cont h ghostenv env size)
    in
    let callpred l coefpat g pats0 pats =
      let g_symb =
        match try_assoc g#name predfammap with
          Some (_, _, _, symb) -> symb
        | None -> List.assoc g#name env
      in
      assert_chunk h ghostenv env l g_symb coef coefpat (pats0 @ pats) (fun h coef ts size ghostenv env -> cont h ghostenv env size)
    in
    match p with
    | Access (l, e, f, rhs) -> access l real_unit_pat e f rhs
    | CallPred (l, g, pats0, pats) -> callpred l real_unit_pat g pats0 pats
    | ExprPred (l, e) ->
      assert_expr env e h env l "Expression is false."; cont h ghostenv env None
    | Sep (l, p1, p2) ->
      assert_pred h ghostenv env p1 coef (fun h ghostenv env size -> assert_pred h ghostenv env p2 coef (fun h ghostenv env _ -> cont h ghostenv env size))
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ _ = cont h ghostenv env None in
      branch
        (fun _ ->
           assume (ev e) (fun _ ->
             assert_pred h ghostenv env p1 coef cont))
        (fun _ ->
           assume (ctxt#mk_not (ev e)) (fun _ ->
             assert_pred h ghostenv env p2 coef cont))
    | SwitchPred (l, e, cs) ->
      let cont h _ _ _ = cont h ghostenv env None in
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, p)::cs ->
          let (_, _, tps, ctorsym) = List.assoc cn purefuncmap in
          let Some pts = zip pats tps in
          let xts = List.map (fun (x, tp) -> (x, get_unique_var_symb x tp)) pts in
          branch
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym (List.map (fun (x, t) -> t) xts)) (fun _ -> assert_pred h (pats @ ghostenv) (xts @ env) p coef cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env None
    | CoefPred (l, coefpat, Access (_, e, f, rhs)) -> access l coefpat e f rhs
    | CoefPred (l, coefpat, CallPred (_, g, pat0, pats)) -> callpred l coefpat g pat0 pats
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
    let (_, (_, _, _, f_symb)) = List.assoc (f#parent, f#name) field_pred_map in
    assert_chunk h [] [("x", t)] l f_symb real_unit DummyPat [LitPat (Var (dummy_loc, "x")); VarPat "y"] (fun h coef ts size ghostenv env ->
      cont h coef (lookup env "y"))
  in
  
  let functypemap =
    let rec iter functypemap ds =
      match ds with
        [] -> List.rev functypemap
      | FuncTypeDecl (l, rt, ftn, xs, (pre, post))::ds ->
        let _ = if List.mem_assoc ftn functypemap then static_error l "Duplicate function type name." in
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        check_pred (xmap @ [("this", PtrType Void)]) pre (fun tenv ->
          let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
          check_pred postmap post (fun _ -> ())
        );
        iter ((ftn, (l, rt, xmap, pre, post))::functypemap) ds
      | _::ds -> iter functypemap ds
    in
    iter [] ds
  in
  
  let (funcmap, prototypes_implemented) =
    match file_type path with
	Java -> let rec iter funcmap prototypes_implemented ds =
      match ds with
        [] -> (funcmap,prototypes_implemented)
      | Meth (l,rt, fn, xs, contract_opt, body,fb,v)::ds->
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        let (cenv, pre, post) =
          match contract_opt with
            None -> static_error l "Non-fixpoint function must have contract."
          | Some (Contract (pre, post)) -> 
            check_pred xmap pre (fun tenv ->
              let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
              check_pred postmap post (fun _ -> ());
            );
            (List.map (fun (x, t) -> (x, Var (dummy_loc, x))) xmap, pre, post)
          | Some (FuncTypeSpec ftn) -> 
            begin
              match try_assoc ftn functypemap with
                None -> static_error l "No such function type."
              | Some (_, rt0, xmap0, pre, post) ->
                if rt <> rt0 then static_error l "Function return type differs from function type return type.";
                begin
                  match zip xmap xmap0 with
                    None -> static_error l "Function parameter count differs from function type parameter count."
                  | Some bs ->
                    let cenv =
                      List.map
                        (fun ((x, t), (x0, t0)) ->
                         if t <> t0 then static_error l ("Type of parameter '" ^ x ^ "' does not match type of function type parameter '" ^ x0 ^ "'.");
                         (x0, Var (dummy_loc, x))
                        )
                        bs
                      @ [("this", FuncNameExpr fn)]
                    in
                    let (_, _, _, symb) = List.assoc ("is_" ^ ftn) isfuncs in
                    ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true));
                    (cenv, pre, post)
                end
            end
        in
        begin
          match try_assoc fn funcmap with
            None -> iter ((fn, (l,Regular,rt, xmap, cenv, pre, post, body,fb,v))::funcmap) prototypes_implemented ds
          | Some (l0,Regular,rt0, xmap0, cenv0, pre0, post0, Some _,fb,v) ->
            if body = None then
              static_error l "Function prototype must precede function implementation."
            else
              static_error l "Duplicate function implementation."
          | Some (l0,Regular,rt0, xmap0, cenv0, pre0, post0, None,fb,v) ->
            if body = None then static_error l "Duplicate function prototype.";
            if rt <> rt0 then static_error l "Function implementation does not match prototype: return types do not match.";
            begin
              match zip xmap xmap0 with
                None -> static_error l "Function implementation does not match prototype: parameter counts do not match."
              | Some pairs ->
                List.iter
                  (fun ((x, t), (x0, t0)) ->
                   if t <> t0 then static_error l ("Function implementation does not match prototype: parameter '" ^ x ^ "': wrong type.")
                  )
                  pairs
            end;
            push();
            let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
            let env0 = List.map (fun (x, e) -> (x, eval None env0_0 e)) cenv0 in
            let _ =
              assume_pred [] [] env0 pre0 real_unit None None (fun h _ env0 ->
                let (Some bs) = zip xmap env0_0 in
                let env_0 = List.map (fun ((p, _), (p0, v)) -> (p, v)) bs in
                let env = List.map (fun (x, e) -> (x, eval None env_0 e)) cenv in
                assert_pred h [] env pre real_unit (fun h _ env _ ->
                  let (result, env) =
                    match rt with
                      None -> (None, env)
                    | Some t -> let result = get_unique_var_symb "result" t in (Some result, ("result", result)::env)
                  in
                  assume_pred h [] env post real_unit None None (fun h _ _ ->
                    let env0 =
                      match result with
                        None -> env0
                      | Some v -> ("result", v)::env0
                    in
                    assert_pred h [] env0 post0 real_unit (fun h _ env0 _ ->
                      if h <> [] then assert_false h env0 l "Function redeclaration leaks heap chunks."
                    )
                  )
                )
              )
            in
            pop();
            iter ((fn, (l,Regular,rt, xmap, cenv, pre, post, body,fb,v))::funcmap) ((fn, l0)::prototypes_implemented) ds
        end
      | _::ds -> iter funcmap prototypes_implemented ds
    in
	let iter2 f funcmap prototypes_implemented=
	  match f with
	  | Func (l, k, rt, fn, xs, contract_opt, body,fb,v) when k <> Fixpoint ->
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        let (cenv, pre, post) =
          match contract_opt with
            None -> static_error l "Non-fixpoint function must have contract."
          | Some (Contract (pre, post)) ->
            check_pred xmap pre (fun tenv ->
              let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
              check_pred postmap post (fun _ -> ())
            );
            (List.map (fun (x, t) -> (x, Var (dummy_loc, x))) xmap, pre, post)
          | Some (FuncTypeSpec ftn) ->
            begin
              match try_assoc ftn functypemap with
                None -> static_error l "No such function type."
              | Some (_, rt0, xmap0, pre, post) ->
                if rt <> rt0 then static_error l "Function return type differs from function type return type.";
                begin
                  match zip xmap xmap0 with
                    None -> static_error l "Function parameter count differs from function type parameter count."
                  | Some bs ->
                    let cenv =
                      List.map
                        (fun ((x, t), (x0, t0)) ->
                         if t <> t0 then static_error l ("Type of parameter '" ^ x ^ "' does not match type of function type parameter '" ^ x0 ^ "'.");
                         (x0, Var (dummy_loc, x))
                        )
                        bs
                      @ [("this", FuncNameExpr fn)]
                    in
                    let (_, _, _, symb) = List.assoc ("is_" ^ ftn) isfuncs in
                    ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true));
                    (cenv, pre, post)
                end
            end
        in
        begin
          match try_assoc fn funcmap with
            None -> (((fn, (l, k, rt, xmap, cenv, pre, post, body,fb,v))::funcmap),prototypes_implemented)
          | Some (l0, k0, rt0, xmap0, cenv0, pre0, post0, Some _,fb,v) ->
            if body = None then
              static_error l "Function prototype must precede function implementation."
            else
              static_error l "Duplicate function implementation."
          | Some (l0, k0, rt0, xmap0, cenv0, pre0, post0, None,fb,v) ->
            if body = None then static_error l "Duplicate function prototype.";
            if k <> k0 then static_error l "Function implementation does not match prototype: modifiers do not match.";
            if rt <> rt0 then static_error l "Function implementation does not match prototype: return types do not match.";
            begin
              match zip xmap xmap0 with
                None -> static_error l "Function implementation does not match prototype: parameter counts do not match."
              | Some pairs ->
                List.iter
                  (fun ((x, t), (x0, t0)) ->
                   if t <> t0 then static_error l ("Function implementation does not match prototype: parameter '" ^ x ^ "': wrong type.")
                  )
                  pairs
            end;
            push();
            let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
            let env0 = List.map (fun (x, e) -> (x, eval None env0_0 e)) cenv0 in
            let _ =
              assume_pred [] [] env0 pre0 real_unit None None (fun h _ env0 ->
                let (Some bs) = zip xmap env0_0 in
                let env_0 = List.map (fun ((p, _), (p0, v)) -> (p, v)) bs in
                let env = List.map (fun (x, e) -> (x, eval None env_0 e)) cenv in
                assert_pred h [] env pre real_unit (fun h _ env _ ->
                  let (result, env) =
                    match rt with
                      None -> (None, env)
                    | Some t -> let result = get_unique_var_symb "result" t in (Some result, ("result", result)::env)
                  in
                  assume_pred h [] env post real_unit None None (fun h _ _ ->
                    let env0 =
                      match result with
                        None -> env0
                      | Some v -> ("result", v)::env0
                    in
                    assert_pred h [] env0 post0 real_unit (fun h _ env0 _ ->
                      if h <> [] then assert_false h env0 l "Function redeclaration leaks heap chunks."
                    )
                  )
                )
              )
            in
            pop();
            (((fn, (l, k, rt, xmap, cenv, pre, post, body,fb,v))::funcmap),((fn, l0)::prototypes_implemented));
        end
		| _ -> (funcmap,prototypes_implemented)
	in
	let rec iter1 (funcmap,prototypes_implemented) ds=
	  match ds with
	  Class(l,cn,meths,fds)::rest->iter1 (iter funcmap prototypes_implemented meths) rest
	  | Func(l,k,rt, fn, xs, contract_opt, body,Static,Public)::rest -> iter1 (iter2 (Func(l,k,rt,fn,xs,contract_opt,body,Static,Public)) funcmap prototypes_implemented) rest
	  | _::rest -> iter1 (funcmap,prototypes_implemented) rest
	  | []-> (List.rev funcmap,List.rev prototypes_implemented)
	in
    iter1 ([],[]) ds
	|_ ->
    let rec iter funcmap prototypes_implemented ds =
      match ds with
        [] -> (List.rev funcmap, List.rev prototypes_implemented)
      | Func (l, k, rt, fn, xs, contract_opt, body,Static,Public)::ds when k <> Fixpoint ->
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        let (cenv, pre, post) =
          match contract_opt with
            None -> static_error l "Non-fixpoint function must have contract."
          | Some (Contract (pre, post)) ->
            check_pred xmap pre (fun tenv ->
              let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
              check_pred postmap post (fun _ -> ())
            );
            (List.map (fun (x, t) -> (x, Var (dummy_loc, x))) xmap, pre, post)
          | Some (FuncTypeSpec ftn) ->
            begin
              match try_assoc ftn functypemap with
                None -> static_error l "No such function type."
              | Some (_, rt0, xmap0, pre, post) ->
                if rt <> rt0 then static_error l "Function return type differs from function type return type.";
                begin
                  match zip xmap xmap0 with
                    None -> static_error l "Function parameter count differs from function type parameter count."
                  | Some bs ->
                    let cenv =
                      List.map
                        (fun ((x, t), (x0, t0)) ->
                         if t <> t0 then static_error l ("Type of parameter '" ^ x ^ "' does not match type of function type parameter '" ^ x0 ^ "'.");
                         (x0, Var (dummy_loc, x))
                        )
                        bs
                      @ [("this", FuncNameExpr fn)]
                    in
                    let (_, _, _, symb) = List.assoc ("is_" ^ ftn) isfuncs in
                    ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true));
                    (cenv, pre, post)
                end
            end
        in
        begin
          match try_assoc fn funcmap with
            None -> iter ((fn, (l, k, rt, xmap, cenv, pre, post, body,Static,Public))::funcmap) prototypes_implemented ds
          | Some (l0, k0, rt0, xmap0, cenv0, pre0, post0, Some _,Static,Public) ->
            if body = None then
              static_error l "Function prototype must precede function implementation."
            else
              static_error l "Duplicate function implementation."
          | Some (l0, k0, rt0, xmap0, cenv0, pre0, post0, None,Static,Public) ->
            if body = None then static_error l "Duplicate function prototype.";
            if k <> k0 then static_error l "Function implementation does not match prototype: modifiers do not match.";
            if rt <> rt0 then static_error l "Function implementation does not match prototype: return types do not match.";
            begin
              match zip xmap xmap0 with
                None -> static_error l "Function implementation does not match prototype: parameter counts do not match."
              | Some pairs ->
                List.iter
                  (fun ((x, t), (x0, t0)) ->
                   if t <> t0 then static_error l ("Function implementation does not match prototype: parameter '" ^ x ^ "': wrong type.")
                  )
                  pairs
            end;
            push();
            let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
            let env0 = List.map (fun (x, e) -> (x, eval None env0_0 e)) cenv0 in
            let _ =
              assume_pred [] [] env0 pre0 real_unit None None (fun h _ env0 ->
                let (Some bs) = zip xmap env0_0 in
                let env_0 = List.map (fun ((p, _), (p0, v)) -> (p, v)) bs in
                let env = List.map (fun (x, e) -> (x, eval None env_0 e)) cenv in
                assert_pred h [] env pre real_unit (fun h _ env _ ->
                  let (result, env) =
                    match rt with
                      None -> (None, env)
                    | Some t -> let result = get_unique_var_symb "result" t in (Some result, ("result", result)::env)
                  in
                  assume_pred h [] env post real_unit None None (fun h _ _ ->
                    let env0 =
                      match result with
                        None -> env0
                      | Some v -> ("result", v)::env0
                    in
                    assert_pred h [] env0 post0 real_unit (fun h _ env0 _ ->
                      if h <> [] then assert_false h env0 l "Function redeclaration leaks heap chunks."
                    )
                  )
                )
              )
            in
            pop();
            iter ((fn, (l, k, rt, xmap, cenv, pre, post, body,Static,Public))::funcmap) ((fn, l0)::prototypes_implemented) ds
        end
      | _::ds -> iter funcmap prototypes_implemented ds
    in
    iter [] [] ds
  in
  
  let nonempty_pred_symbs = List.map (fun (_, (_, (_, _, _, symb))) -> symb) field_pred_map in
  
  let check_leaks h env l msg =
    match file_type path with
	Java -> ()
	| _ -> let (_, _, _, chars_symb) = List.assoc "chars" predfammap in
    let (_, _, _, string_literal_symb) = List.assoc "string_literal" predfammap in
    let (stringlitchunks, otherchunks) =
      let rec iter stringlitchunks otherchunks h =
        match h with
          [] -> (stringlitchunks, otherchunks)
        | ((g, coef, ts, _) as chunk)::h when g == string_literal_symb && (file_type path) <> Java -> iter (chunk::stringlitchunks) otherchunks h
        | chunk::h -> iter stringlitchunks (chunk::otherchunks) h
      in
      iter [] [] h
    in
    let rec iter stringlitchunks otherchunks =
      match stringlitchunks with
        [] ->
        if otherchunks = [] then () else assert_false h env l msg
      | (_, coef, [arr; cs], _)::stringlitchunks ->
        let rec consume_chars_chunk otherchunks h =
          match h with
            [] -> assert_false h env l "At function exit: string_literal chunk without matching chars chunk."
          | (g, coef', [arr'; cs'], _)::h when g == chars_symb && (file_type path) <> Java && definitely_equal coef coef' && definitely_equal arr arr' && definitely_equal cs cs' -> iter stringlitchunks (otherchunks @ h)
          | chunk::h -> consume_chars_chunk (chunk::otherchunks) h
        in
        consume_chars_chunk [] otherchunks
    in
    iter stringlitchunks otherchunks
  in 
  let eval_non_pure is_ghost_expr h env e =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg -> assert_term t h env l msg) in
    eval_core assert_term (Some (fun l t f -> read_field h env l t f)) env e
  in 
  
  let eval_h is_ghost_expr h env e cont =
    match e with
      StringLit (l, s)->
	    if(file_type path <> Java) then
		  let (_, _, _, chars_symb) = List.assoc "chars" predfammap in
		  let (_, _, _, string_literal_symb) = List.assoc "string_literal" predfammap in
		  let (_, _, _, chars_contains_symb) = List.assoc "chars_contains" purefuncmap in
          let value = get_unique_var_symb "stringLiteral" (PtrType Char) in
          let cs = get_unique_var_symb "stringLiteralChars" (InductiveType "chars") in
          let coef = get_unique_var_symb "stringLiteralCoef" RealType in
            assume (ctxt#mk_app chars_contains_symb [cs; ctxt#mk_intlit 0]) (fun () -> (* chars_contains(cs, 0) == true *)
              cont ((chars_symb, coef, [value; cs], None)::(string_literal_symb, coef, [value; cs], None)::h) value
            )
	    else
		  cont h (eval_non_pure is_ghost_expr h env e)
    | e -> cont h (eval_non_pure is_ghost_expr h env e)
  in
  
  let prototypes_used : (string * loc) list ref = ref [] in
  
  let register_prototype_used l g =
    if not (List.mem (g, l) !prototypes_used) then
      prototypes_used := (g, l)::!prototypes_used
  in
  
  let assume_is_of_type t tp cont =
    match tp with
      IntType -> assume (ctxt#mk_and (ctxt#mk_le min_int_term t) (ctxt#mk_le t max_int_term)) cont
    | _ -> cont()
  in
  
  let rec verify_stmt pure leminfo sizemap tenv ghostenv h env s tcont return_cont =
    stats#stmtExec;
    let l = stmt_loc s in
    if verbose then print_endline (string_of_loc l ^ ": Executing statement");
    let eval0 = eval in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure pure h env e in
    let eval_h0 = eval_h in
    let eval_h h env e cont = if not pure then check_ghost ghostenv l e; eval_h pure h env e cont in
    let rec evhs h env es cont =
      match es with
        [] -> cont h []
      | e::es -> eval_h h env e (fun h v -> evhs h env es (fun h vs -> cont h (v::vs)))
    in 
    let ev e = eval env e in
    let cont = tcont sizemap tenv ghostenv in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context."
    in
    let vartp l x = match try_assoc x tenv with None -> static_error l "No such variable." | Some tp -> tp in
    let call_stmt l xo g pats fb=
      (
      match try_assoc g funcmap with
        None -> (
        match try_assoc g purefuncmap with
          None -> static_error l ("No such function: " ^ g)
        | Some (lg, rt, pts, gs) -> (
          match xo with
            None -> static_error l "Cannot write call of pure function as statement."
          | Some x ->
            let tpx = vartp l x in
            let _ = check_expr_t tenv (CallExpr (l, g, [], pats,fb)) in
            let _ = check_assign l x in
            let ts = List.map (function (LitPat e) -> ev e) pats in
            cont h (update env x (ctxt#mk_app gs ts))
          )
        )
      | Some (lg,k, tr, ps, cenv0, pre, post, body,fbf,v) ->
	    if fb <>fbf then static_error l ("Wrong function binding "^(tostring fb)^" instead of "^(tostring fbf));
        if body = None then register_prototype_used lg g;
        let _ = if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." in
        let ys = List.map (function (p, t) -> p) ps in
        let _ =
          match zip pats ps with
            None -> static_error l "Incorrect number of arguments."
          | Some bs ->
            List.iter
              (function (LitPat e, (x, tp)) ->
                 check_expr_t tenv e tp
              ) bs
        in
        evhs h env (List.map (function (LitPat e) -> e) pats) (fun h ts ->
        let Some env' = zip ys ts in
        let cenv = List.map (fun (x, e) -> (x, eval0 None env' e)) cenv0 in
        with_context PushSubcontext (fun () ->
        assert_pred h ghostenv cenv pre real_unit (fun h ghostenv' env' chunk_size ->
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
                  | (p, coef, ts, _)::_ when List.memq p nonempty_pred_symbs && coef == real_unit -> true
                  | _::h -> nonempty h
                in
                if nonempty h then
                  ()
                else (
                  match indinfo with
                    None ->
                    begin
                      match chunk_size with
                        Some k when k < 0 -> ()
                      | _ ->
                        with_context (Executing (h, env', l, "Checking recursion termination")) (fun _ ->
                          assert_false h env l "Recursive lemma call does not decrease the heap (no full field chunks left) or the derivation depth of the first chunk and there is no inductive parameter."
                        )
                    end
                  | Some x -> (
                    match try_assq (List.assoc x env') sizemap with
                      Some k when k < 0 -> ()
                    | _ ->
                      with_context (Executing (h, env', l, "Checking recursion termination")) (fun _ ->
                        assert_false h env l "Recursive lemma call does not decrease the heap (no full field chunks left) or the inductive parameter."
                      )
                    )
                )
              else
                static_error l "A lemma can call only preceding lemmas or itself."
          in
          let r = match tr with None -> None | Some t -> Some (get_unique_var_symb "result" t, t) in
          let env'' = match r with None -> env' | Some (r, t) -> update env' "result" r in
          assume_pred h ghostenv' env'' post real_unit None None (fun h _ _ ->
            let env =
              match xo with
                None -> env
              | Some x ->
                let tpx = vartp l x in
                let _ = check_assign l x in
                begin
                  match r with
                    None -> static_error l "Call does not return a result."
                  | Some (r, t) -> expect_type l t tpx; update env x r
                end
            in
            with_context PopSubcontext (fun () -> cont h env)
          )
        )
        )
        )
      )
    in 
    match s with
      PureStmt (l, s) ->
      verify_stmt true leminfo sizemap tenv ghostenv h env s tcont return_cont
    | Assign (l, x, CallExpr (lc, "malloc", [], args,Static)) ->
      begin
        match args with
          [LitPat (SizeofExpr (lsoe, StructTypeExpr (ltn, tn)))] ->
          let tpx = vartp l x in
          let _ = check_assign l x in
          let (_, fds_opt) = List.assoc tn structmap in
          let fds =
            match fds_opt with
              Some fds -> fds
            | None -> static_error l "Argument of sizeof cannot be struct type declared without a body."
          in
          let _ =
            match tpx with
              PtrType (StructType sn) when sn = tn -> ()
            | _ -> static_error l ("Type mismatch: actual: '" ^ string_of_type tpx ^ "'; expected: 'struct " ^ tn ^ " *'.")
          in
          let result = get_unique_var_symb "block" tpx in
          branch
            (fun () ->
               assume_eq result (ctxt#mk_intlit 0) (fun () ->
                 cont h ((x, result)::env)
               )
            )
            (fun () ->
               assume_neq result (ctxt#mk_intlit 0) (fun () ->
                 let rec iter h fds =
                   match fds with
                     [] ->
                     let (_, (_, _, _, malloc_block_symb)) = List.assoc tn malloc_block_pred_map in
                     cont (h @ [(malloc_block_symb, real_unit, [result], None)]) (update env x result)
                   | (f, (lf, t))::fds ->
                     let fref = new fieldref f in
                     fref#set_parent tn; fref#set_range t; assume_field h fref result (get_unique_var_symb "value" t) real_unit (fun h -> iter h fds)
                 in
                 iter h fds
               )
            )
        | _ -> call_stmt l (Some x) "malloc" args Static
      end
	| Assign (l, x, CallExpr (lc, "new", [], args,Static)) ->
	  begin match args with
	    [] -> 
          let tpx = vartp l x in
          let _ = check_assign l x in
          let tn =
            match tpx with
              ObjType sn -> sn
            | _ -> static_error l ("Type mismatch")
          in
		  let (_,_,fds_opt) = List.assoc tn classmap in
		  let fds =
            match fds_opt with
              Some fds -> fds
            | None -> static_error l "Argument of sizeof cannot be struct type declared without a body."
          in
          let result = get_unique_var_symb "block" tpx in
               assume_neq result (ctxt#mk_intlit 0) (fun () ->
                 let rec iter h fds =
                   match fds with
                     [] ->
                     let (_, (_, _, _, malloc_block_symb)) = List.assoc tn malloc_block_pred_map in
                     cont (h @ [(malloc_block_symb, real_unit, [result], None)]) (update env x result)
                   | (f, (lf, t))::fds ->
                     let fref = new fieldref f in
                     fref#set_parent tn; fref#set_range t; assume_field h fref result (get_unique_var_symb "value" t) real_unit (fun h -> iter h fds)
                 in
                 iter h fds
               )
		 | _-> call_stmt l (Some x) "malloc" args Static
		end
    | CallStmt (l, "assume_is_int", [Var (lv, x) as e],Static) ->
      if not pure then static_error l "This function may be called only from a pure context.";
      if List.mem x ghostenv then static_error l "The argument for this call must be a non-ghost variable.";
      let tp = check_expr tenv e in
      assume_is_of_type (ev e) tp (fun () -> cont h env)
    | CallStmt (l, "free", args,Static) ->
      begin
        match List.map (check_expr tenv) args with
          [PtrType (StructType tn)] ->
          let [arg] = args in
          let _ = if pure then static_error l "Cannot call a non-pure function from a pure context." in
          let fds =
            match flatmap (function (Struct (ls, sn, Some fds)) when sn = tn -> [fds] | _ -> []) ds with
              [fds] -> fds
            | [] -> static_error l "Freeing an object of a struct type declared without a body is not supported."
          in
          let arg = ev arg in
          let rec iter h fds =
            match fds with
              [] -> cont h env
            | (Field (lf, t, f,Instance))::fds ->
              let fref = new fieldref f in
              fref#set_parent tn;
              get_field h arg fref l (fun h coef _ -> if not (definitely_equal coef real_unit) then assert_false h env l "Free requires full field chunk permissions."; iter h fds)
          in
          let (_, (_, _, _, malloc_block_symb)) = List.assoc tn malloc_block_pred_map in
          assert_chunk h [] [("x", arg)] l malloc_block_symb real_unit DummyPat [LitPat (Var (l, "x"))] (fun h coef _ _ _ _ -> if not (definitely_equal coef real_unit) then assert_false h env l "Free requires full malloc_block permission."; iter h fds)
        | _ -> call_stmt l None "free" (List.map (fun e -> LitPat e) args) Static
      end
    | Assign (l, x, CallExpr (lc, g, [], pats,fb)) ->
      call_stmt l (Some x) g pats fb
    | Assign (l, x, e) -> 
      let tpx = vartp l x in
      let _ = check_expr_t tenv e tpx in
      let _ = check_assign l x in
      eval_h h env e (fun h v -> cont h ((x, v)::env));
    | DeclStmt (l, te, x, e) ->
      if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.");
      let t = check_pure_type te in
      let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
      verify_stmt pure leminfo sizemap ((x, t)::tenv) ghostenv h env (Assign (l, x, e)) tcont return_cont (* BUGBUG: e should be typechecked outside of the scope of x *)
	  ;
    | Write (l, e, f, rhs) ->
      let _ = if pure then static_error l "Cannot write in a pure context." in
      let tp = check_deref l tenv e f in
      let _ = check_expr_t tenv rhs tp in
      eval_h h env e (fun h t ->
        let (_, (_, _, _, f_symb)) = List.assoc (f#parent, f#name) field_pred_map in
        get_field h t f l (fun h coef _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a field requires full field permission.";
          cont ((f_symb, real_unit, [t; ev rhs], None)::h) env)
      )
    | CallStmt (l, g, es,fb) ->
      call_stmt l None g (List.map (fun e -> LitPat e) es) fb
    | IfStmt (l, e, ss1, ss2) ->
      let _ = check_expr_t tenv e boolt in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      branch
        (fun _ -> assume (ev e) (fun _ -> verify_cont pure leminfo sizemap tenv ghostenv h env ss1 tcont return_cont))
        (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> verify_cont pure leminfo sizemap tenv ghostenv h env ss2 tcont return_cont))
    | SwitchStmt (l, e, cs) ->
      let tp = check_expr tenv e in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let (tn, (_, ctormap)) =
        match tp with
          InductiveType i -> (i, List.assoc i inductivemap)
        | _ -> static_error l "Switch statement operand is not an inductive value."
      in
      let t = ev e in
      let rec iter ctors cs =
        match cs with
          [] ->
          begin
          match ctors with
            [] -> success()
          | _ -> static_error l ("Missing clauses: " ^ String.concat ", " ctors)
          end
        | SwitchStmtClause (lc, cn, pats, ss)::cs ->
          let pts =
            match try_assoc cn ctormap with
              None -> static_error lc ("Not a constructor of type " ^ tn)
            | Some (l, pts) -> pts
          in
          let _ = if not (List.mem cn ctors) then static_error lc "Constructor already handled in earlier clause." in
          let ptenv =
            let rec iter ptenv pats pts =
              match (pats, pts) with
                ([], []) -> List.rev ptenv
              | (pat::pats, tp::pts) ->
                if List.mem_assoc pat tenv then static_error lc ("Pattern variable '" ^ pat ^ "' hides existing local variable '" ^ pat ^ "'.");
                if List.mem_assoc pat ptenv then static_error lc "Duplicate pattern variable.";
                iter ((pat, tp)::ptenv) pats pts
              | ([], _) -> static_error lc "Too few arguments."
              | _ -> static_error lc "Too many arguments."
            in
            iter [] pats pts
          in
          let xts = List.map (fun (x, tp) -> (x, get_unique_var_symb x tp)) ptenv in
          let (_, _, _, ctorsym) = List.assoc cn purefuncmap in
          let sizemap =
            match try_assq t sizemap with
              None -> sizemap
            | Some k -> List.map (fun (x, t) -> (t, k - 1)) xts @ sizemap
          in
          branch
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym (List.map (fun (x, t) -> t) xts)) (fun _ -> verify_cont pure leminfo sizemap (ptenv @ tenv) (pats @ ghostenv) h (xts @ env) ss tcont return_cont))
            (fun _ -> iter (List.filter (function cn' -> cn' <> cn) ctors) cs)
      in
      iter (List.map (function (cn, _) -> cn) ctormap) cs
    | Assert (l, p) ->
      check_pred tenv p (fun tenv ->
        assert_pred h ghostenv env p real_unit (fun _ ghostenv env _ ->
          tcont sizemap tenv ghostenv h env
        )
      )
    | Open (l, g, is, pats, coefpat) ->
      let fns = check_funcnamelist is in
      let (ps, p) =
        match try_assoc (g, fns) predinstmap with
          None -> static_error l "No such predicate family instance."
        | Some (l, ps, body) -> (ps, body)
      in
      let tenv = match coefpat with None -> tenv | Some coefpat -> check_pat l tenv RealType coefpat in
      let tenv' = check_pats l tenv (List.map (fun (x, t) -> t) ps) pats in
      let pats = List.map (fun fn -> LitPat (FuncNameExpr fn)) fns @ pats in
      let (_, _, _, g_symb) = List.assoc g predfammap in
      let coefpat = match coefpat with None -> DummyPat | Some coefpat -> coefpat in
      assert_chunk h ghostenv env l g_symb real_unit coefpat pats (fun h coef ts chunk_size ghostenv env ->
        let ts = drop (List.length fns) ts in
        let ys = List.map (function (p, t) -> p) ps in
        let Some env' = zip ys ts in
        let body_size = match chunk_size with None -> None | Some k -> Some (k - 1) in
        with_context PushSubcontext (fun () ->
          assume_pred h ghostenv env' p coef body_size body_size (fun h _ _ ->
            with_context PopSubcontext (fun () -> tcont sizemap tenv' ghostenv h env)
          )
        )
      )
    | Close (l, g, is, pats, coef) ->
      let fns = check_funcnamelist is in
      let (ps, p) =
        match try_assoc (g, fns) predinstmap with
          None -> static_error l "No such predicate family instance."
        | Some (l, ps, body) -> (ps, body)
      in
      let _ =
        match zip pats ps with
          None -> static_error l "Wrong number of arguments."
        | Some bs ->
          List.iter (function (LitPat e, (_, tp)) -> check_expr_t tenv e tp) bs
      in
      let ts = List.map (function LitPat e -> ev e) pats in
      let coef = match coef with None -> real_unit | Some (LitPat coef) -> check_expr_t tenv coef RealType; ev coef | _ -> static_error l "Coefficient in close statement must be expression." in
      let ys = List.map (function (p, t) -> p) ps in
      let Some env' = zip ys ts in
      let (_, _, _, g_symb) = List.assoc g predfammap in
      with_context PushSubcontext (fun () ->
        assert_pred h ghostenv env' p coef (fun h _ _ _ ->
          with_context PopSubcontext (fun () -> cont ((g_symb, coef, List.map (fun fn -> List.assoc fn funcnameterms) fns @ ts, None)::h) env)
        )
      )
    | ReturnStmt (l, Some e) ->
      let tp = match try_assoc "#result" tenv with None -> static_error l "Void function cannot return a value." | Some tp -> tp in
      let _ = if pure && not (List.mem "#result" ghostenv) then static_error l "Cannot return from a regular function in a pure context." in
      let _ = check_expr_t tenv e tp in
      return_cont h (Some (ev e))
    | ReturnStmt (l, None) -> return_cont h None
    | WhileStmt (l, e, p, ss) ->
      let _ = if pure then static_error l "Loops are not yet supported in a pure context." in
      let _ = check_expr_t tenv e boolt in
      check_ghost ghostenv l e;
      let xs = block_assigned_variables ss in
      let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
      check_pred tenv p (fun tenv' ->
      assert_pred h ghostenv env p real_unit (fun h _ _ _ ->
        let bs = List.map (fun x -> (x, get_unique_var_symb x (List.assoc x tenv))) xs in
        let env = bs @ env in
        branch
          (fun _ ->
             assume_pred [] ghostenv env p real_unit None None (fun h' ghostenv' env' ->
               assume (eval0 (Some (fun l t f -> read_field h' env l t f)) env e) (fun _ ->
                 verify_cont pure leminfo sizemap tenv' ghostenv' h' env' ss (fun _ _ _ h'' env ->
                   let env = List.filter (fun (x, _) -> List.mem_assoc x tenv) env in
                   assert_pred h'' ghostenv env p real_unit (fun h''' _ _ _ ->
                     check_leaks h''' env l "Loop leaks heap chunks."
                   )
                 ) (fun h'' retval -> return_cont (h'' @ h) retval)
               )
             )
          )
          (fun _ ->
             assume_pred h ghostenv env p real_unit None None (fun h ghostenv' env' ->
               assume (ctxt#mk_not (eval0 (Some (fun l t f -> read_field h env l t f)) env e)) (fun _ ->
                 tcont sizemap tenv' ghostenv' h env')))
      )
      )
    | BlockStmt (l, ss) ->
      let cont h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      verify_cont pure leminfo sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env -> cont h env) return_cont
  and
    verify_cont pure leminfo sizemap tenv ghostenv h env ss cont return_cont =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        verify_stmt pure leminfo sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          verify_cont pure leminfo sizemap tenv ghostenv h env ss cont return_cont
        ) return_cont
      )
  in

  let rec verify_funcs lems funcs =
    match funcs with
    | [] -> ()
    | (g, (l, Lemma, rt, ps, cenv0, pre, post, None,fb,v))::funcs ->
      verify_funcs (g::lems) funcs
    | (g, (l, k, rt, ps, cenv0, pre, post, Some ss,fb,v))::funcs ->
      let _ = push() in
      let env = List.map (function (p, t) -> (p, get_unique_var_symb p t)) ps in
      let (sizemap, indinfo) =
        match ss with
          [SwitchStmt (_, Var (_, x), _)] -> (
          match try_assoc x env with
            None -> ([], None)
          | Some t -> ([(t, 0)], Some x)
          )
        | _ -> ([], None)
      in
      let pts = ps in
      let tenv = pts in
      let tenv = List.map (fun (x, e) -> (x, check_expr tenv e)) cenv0 in
      let (tenv, rxs) =
        match rt with
          None -> (tenv, [])
        | Some rt -> (("#result", rt)::tenv, ["#result"])
      in
      let (in_pure_context, leminfo, lems', ghostenv) =
        if k = Lemma then
          (true, Some (lems, g, indinfo), g::lems, List.map (function (p, t) -> p) ps @ rxs)
        else
          (false, None, lems, [])
      in
      check_pred tenv pre (fun tenv ->
      let env = List.map (fun (x, e) -> (x, eval None env e)) cenv0 in
      let _ =
        assume_pred [] ghostenv env pre real_unit (Some 0) None (fun h ghostenv env ->
          let do_return h env_post =
		    match file_type path with
			Java -> assert_pred h ghostenv env_post post real_unit (fun h ghostenv env size_first ->
              with_context (Executing (h, env, l, "Checking emptyness.")) (fun _ ->
                check_leaks h env l "Function leaks heap chunks."
              )
            )
			|_ ->
             assert_pred h ghostenv env_post post real_unit (fun h ghostenv env size_first ->
              with_context (Executing (h, env, l, "Checking emptyness.")) (fun _ ->
                check_leaks h env l "Function leaks heap chunks."
              )
            )
          in
          let return_cont h retval =
            match (rt, retval) with
              (None, None) -> do_return h env
            | (Some tp, Some t) -> do_return h (("result", t)::env)
            | (None, Some _) -> assert_false h env l "Void function returns a value."
            | (Some _, None) -> assert_false h env l "Non-void function does not return a value."
          in
          verify_cont in_pure_context leminfo sizemap tenv ghostenv h env ss (fun _ _ _ h _ -> return_cont h None) return_cont
        )
      in
      let _ = pop() in
      verify_funcs lems' funcs
      )
    | _::funcs -> verify_funcs lems funcs
  in
  
  verify_funcs [] funcmap;
  
  let create_manifest_file() =
    let manifest_filename = Filename.chop_extension path ^ ".vfmanifest" in
    let file = open_out manifest_filename in
    let sorted_lines protos =
      let lines = List.map (fun (g, (((_, path), _, _), _)) -> path ^ "#" ^ g) protos in
      List.sort compare lines
    in
    do_finally (fun () ->
      List.iter (fun line -> output_string file (".requires " ^ line ^ "\n")) (sorted_lines !prototypes_used);
      List.iter (fun line -> output_string file (".provides " ^ line ^ "\n")) (sorted_lines prototypes_implemented)
    ) (fun () -> close_out file)
  in
  create_manifest_file()

let verify_program_with_stats ctxt print_stats verbose path stream streamSource reportKeyword reportGhostRange =
  do_finally
    (fun () -> verify_program_core ctxt verbose path stream streamSource reportKeyword reportGhostRange)
    (fun () -> if print_stats then stats#printStats)

class virtual prover_client =
  object
    method virtual run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit
  end

let prover_table: (string * (prover_client -> unit)) list ref = ref []

let register_prover name f =
  prover_table := (name, f)::!prover_table

let lookup_prover prover =
  match prover with
    None ->
    begin
      match !prover_table with
        [] -> assert false
      | (_, f)::_ -> f
    end
  | Some name ->
    begin
      match try_assoc name !prover_table with
        None -> failwith ("No such prover: " ^ name)
      | Some f -> f
    end
      
let verify_program prover print_stats verbose path stream streamSource reportKeyword reportGhostRange =
  lookup_prover prover
    (object
       method run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit =
         fun ctxt -> verify_program_with_stats ctxt print_stats verbose path stream streamSource reportKeyword reportGhostRange
     end)

let remove_dups bs =
  let rec iter bs0 bs =
    match bs with
      [] -> List.rev bs0
    | (x, v)::bs ->
      if List.mem_assoc x bs0 then iter bs0 bs else iter ((x, v)::bs0) bs
  in
  iter [] bs

exception LinkError of string

let link_program isLibrary modulepaths =
  let rec iter impls modulepaths =
    match modulepaths with
      [] -> impls
    | modulepath::modulepaths ->
      let manifest_path = Filename.chop_extension modulepath ^ ".vfmanifest" in
      let lines =
        let file = open_in manifest_path in
        do_finally (fun () ->
          let rec iter () =
            try
              let line = input_line file in
              line::iter()
            with
              End_of_file -> []
          in
          iter()
        ) (fun () -> close_in file)
      in
      let rec iter0 impls' lines =
        match lines with
          [] -> iter impls' modulepaths
        | line::lines ->
          let space = String.index line ' ' in
          let command = String.sub line 0 space in
          let symbol = String.sub line (space + 1) (String.length line - space - 1) in
          begin
            match command with
              ".requires" -> if List.mem symbol impls then iter0 impls' lines else raise (LinkError ("Module '" ^ modulepath ^ "': unsatisfied requirement '" ^ symbol ^ "'."))
            | ".provides" -> iter0 (symbol::impls') lines
          end
      in
      iter0 impls lines
  in
  let impls = iter [] modulepaths in
  if not isLibrary then
    if not (List.mem "prelude.h#main" impls) then raise (LinkError ("Program does not implement 'main'. Use the '-shared' option to suppress this error."))