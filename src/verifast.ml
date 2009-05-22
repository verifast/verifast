open Proverapi
open Big_int

let manifest_map: (string * string list) list ref = ref []
let jardeps_map: (string * string list) list ref = ref []

let ($.) f x = f x

let intersect xs ys = List.filter (fun x -> List.mem x ys) xs
let flatmap f xs = List.concat (List.map f xs)
let rec drop n xs = if n = 0 then xs else drop (n - 1) (List.tl xs)
let take_drop n xs =
  let rec iter left right k =
    if k = 0 then
      (left, right)
    else
      match right with
        [] -> (left, right)
      | x::right -> iter (x::left) right (k - 1)
  in
  iter [] xs n
let rec list_make n x = if n = 0 then [] else x::list_make (n - 1) x

let remove f xs = List.filter (fun x -> not (f x)) xs

let rec distinct xs =
  match xs with
    [] -> true
  | x::xs -> not (List.mem x xs) && distinct xs

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

let imap f xs =
  let rec imapi i xs =
    match xs with
      [] -> []
    | x::xs -> f i x::imapi (i + 1) xs
  in
  imapi 0 xs

let list_remove_dups xs =
  let rec iter ys xs =
    match xs with
      [] -> List.rev ys
    | x::xs -> if List.mem x ys then iter ys xs else iter (x::ys) xs
  in
  iter [] xs

let startswith s s0 =
  String.length s0 <= String.length s && String.sub s 0 (String.length s0) = s0

let chop_suffix s s0 =
  let n0 = String.length s0 in
  let n = String.length s in
  if n0 <= n && String.sub s (n - n0) n0 = s0 then Some (String.sub s 0 (n - n0)) else None

let try_assoc2 x xys1 xys2 =
  match try_assoc x xys1 with
    None -> try_assoc x xys2
  | result -> result

let assoc2 x xys1 xys2 =
  let (Some y) = try_assoc2 x xys1 xys2 in y

let bindir = Filename.dirname Sys.executable_name
let rtdir= Filename.concat bindir "rt"

let banner =
  "Verifast " ^ Vfversion.version ^ " for C and Java (released " ^ Vfversion.release_date ^ ") <http://www.cs.kuleuven.be/~bartj/verifast/>\n" ^
  "By Bart Jacobs <http://www.cs.kuleuven.be/~bartj/> and Frank Piessens, with contributions by Cedric Cuypers, Lieven Desmet, and Jan Smans\n" ^
  "Powered by the excellent SMT solver Z3 <http://research.microsoft.com/projects/z3> by Leonardo de Maura and Nikolaj Bjorner. The Z3 license applies. See Z3.LICENSE.txt."

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
  | PreprocessorSymbol of string
  | Eol
  | ErrorToken

type srcpos = ((string * string) * int * int)
type loc = (srcpos * srcpos)

exception ParseException of loc * string

(* The lexer *)

type range_kind =
    KeywordRange
  | GhostKeywordRange
  | GhostRange
  | GhostRangeDelimiter
  | CommentRange
  | ErrorRange

let make_lexer_core keywords path stream reportRange inComment inGhostRange exceptionOnError reportShouldFail =
  let in_comment = ref inComment in
  let in_ghost_range = ref inGhostRange in
  
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
  let token_srcpos = ref (path, 1, 1) in

  let current_srcpos() = (path, !line, Stream.count stream - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in

  let in_single_line_annotation = ref false in
  
  let ghost_range_start: srcpos option ref = ref (if inGhostRange then Some (current_srcpos()) else None) in
  
  let ignore_eol = ref true in
  
  let error msg =
      raise (Stream.Error msg)
  in
  
  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  let ident_or_keyword id isAlpha =
    try
      let t = Hashtbl.find kwd_table id in
      if isAlpha then
        reportRange (if !ghost_range_start = None then KeywordRange else GhostKeywordRange) (current_loc());
      t
    with
      Not_found ->
      let n = String.length id in
      if n > 2 && id.[n - 2] = '_' && id.[n - 1] = 'H' then PreprocessorSymbol id else Ident id
  and keyword_or_error c =
    let s = String.make 1 c in
    try Hashtbl.find kwd_table s with
      Not_found -> error "Illegal character"
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
    if !in_comment then
    begin
      in_comment := false;
      multiline_comment strm__
    end
    else
    let new_line strm__ =
      new_loc_line strm__;
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        ghost_range_end();
        Some (Kwd "@*/")
      ) else if !ignore_eol then
        next_token strm__
      else
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
         '?' | '@' | '\\' | '~' | '^' | '|' as c) ->
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
            Stream.Failure -> error "Bad character literal."
        in
        begin match Stream.peek strm__ with
          Some '\'' -> Stream.junk strm__; Some (Char c)
        | _ -> error "Single quote expected."
        end
    | Some '"' ->
        start_token();
        Stream.junk strm__;
        let s = strm__ in reset_buffer (); Some (String (string s))
    | Some '-' -> start_token(); Stream.junk strm__; neg_number strm__
    | Some '/' -> start_token(); Stream.junk strm__; maybe_comment strm__
    | Some c -> start_token(); Stream.junk strm__; Some (keyword_or_error c)
    | _ ->
      in_ghost_range := !ghost_range_start <> None;
      ghost_range_end();
      None
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
    | _ ->
      let s = get_string() in
      if s = "@*/" then
      begin
        ghost_range_end();
        reportRange GhostRangeDelimiter (current_loc())
      end;
      Some (ident_or_keyword s false)
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
            Stream.Failure -> error "Bad string literal."
        in
        let s = strm__ in store c; string s
    | Some c when c < ' ' -> raise Stream.Failure
    | Some c -> Stream.junk strm__; let s = strm__ in store c; string s
    | _ -> raise Stream.Failure
  and char (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\\' ->
        Stream.junk strm__;
        begin try escape strm__ with
          Stream.Failure -> error "Bad character literal."
        end
    | Some c when c < ' ' -> raise Stream.Failure
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
            | _ -> error "Bad escape sequence."
            end
        | _ -> error "Bad escape sequence."
        end
    | Some c when c < ' ' -> raise Stream.Failure
    | Some c -> Stream.junk strm__; c
    | _ -> raise Stream.Failure
  and ghost_range_end() =
    match !ghost_range_start with
      None -> ()
    | Some sp -> reportRange GhostRange (sp, current_srcpos()); ghost_range_start := None
  and maybe_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '/' ->
      Stream.junk strm__;
      (
        match Stream.peek strm__ with
          Some '@' ->
          begin
            Stream.junk strm__;
            if !ghost_range_start <> None then raise Stream.Failure;
            in_single_line_annotation := true;
            ghost_range_start := Some !token_srcpos;
            reportRange GhostRangeDelimiter (current_loc());
            Some (Kwd "/*@")
          end
        | _ ->
          if !in_single_line_annotation then (
            in_single_line_annotation := false;
            ghost_range_end();
            single_line_comment strm__;
            Some (Kwd "@*/")
          ) else (
            single_line_comment strm__; next_token strm__
          )
      )
    | Some '*' ->
      Stream.junk strm__;
      (
        match Stream.peek strm__ with
          Some '@' ->
          Stream.junk strm__;
          if !ghost_range_start <> None then raise Stream.Failure;
          ghost_range_start := Some !token_srcpos;
          reportRange GhostRangeDelimiter (current_loc());
          Some (Kwd "/*@")
        | _ -> multiline_comment strm__
      )
    | _ -> Some (keyword_or_error '/')
  and single_line_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '~' -> Stream.junk strm__; reportShouldFail (current_loc()); single_line_comment_rest strm__
    | _ -> single_line_comment_rest strm__
  and single_line_comment_rest (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\010' | Some '\013' | None -> reportRange CommentRange (current_loc())
    | Some c -> Stream.junk strm__; single_line_comment_rest strm__
    | _ -> raise Stream.Failure
  and multiline_comment (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '*' ->
      (
        Stream.junk strm__;
        (
          match Stream.peek strm__ with
            Some '/' -> (Stream.junk strm__; reportRange CommentRange (current_loc()); next_token strm__)
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
    | None when not exceptionOnError ->
      in_ghost_range := !ghost_range_start <> None;
      in_comment := true;
      reportRange CommentRange (current_loc());
      None
    | _ -> (Stream.junk strm__; multiline_comment strm__)
  in
  (current_loc,
   ignore_eol,
   Stream.from (fun count ->
     (try
        match next_token stream with
          Some t -> Some (current_loc(), t)
        | None -> None
      with
        Stream.Error msg when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      | Stream.Failure when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      )),
   in_comment,
   in_ghost_range)

let make_lexer keywords path stream reportRange reportShouldFail =
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_core keywords path stream reportRange false false true reportShouldFail in
  (loc, ignore_eol, token_stream)

type type_ =
    Bool
  | Void
  | IntType
  | RealType
  | Char
  | StructType of string
  | PtrType of type_
  | FuncType of string
  | InductiveType of string * type_ list
  | PredType of type_ list
  | ObjType of string
  | BoxIdType (* box type*)
  | HandleIdType (* handle type *)
  | AnyType (* any type, kan aan alle inductieve datatypes toegekend worden*)
  | TypeParam of string (* type param, tussen <>*)
  | InferredType of type_ option ref (* inferred type *)

type prover_type = ProverInt | ProverBool | ProverReal | ProverInductive

type type_expr =
    StructTypeExpr of loc * string
  | PtrTypeExpr of loc * type_expr
  | ArrayTypeExpr of loc * type_expr
  | ManifestTypeExpr of loc * type_
  | IdentTypeExpr of loc * string
  | ConstructedTypeExpr of loc * string * type_expr list
  | PredTypeExpr of loc * type_expr list

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

class predref (name: string) =
  object
    val mutable domain: type_ list option = None
    val mutable inputParamCount: int option option = None
    method name = name
    method domain = match domain with None -> assert false | Some d -> d
    method inputParamCount = match inputParamCount with None -> assert false | Some c -> c
    method set_domain d = domain <- Some d
    method set_inputParamCount c = inputParamCount <- Some c
  end

type
  ident_scope =
    LocalVar
  | PureCtor
  | FuncName
  | PredFamName

type
  operator = Add | Sub | Le | Lt | Eq | Neq | And | Or | Not | Mul | Div
and
  expr =
    True of loc
  | False of loc
  | Null of loc
  | Var of loc * string * ident_scope option ref
  | Operation of loc * operator * expr list * type_ list option ref (* voor operaties met bovenstaande operators*)
  | IntLit of loc * big_int * type_ option ref (* int literal*)
  | StringLit of loc * string (* string literal *)
  | ClassLit of loc * string (* class literal in java *)
  | Read of loc * expr * fieldref (* lezen van een veld; hergebruiken voor java field acces *)
  | Deref of loc * expr * type_ option ref (* pointee type *) (* pointer dereference *)
  | CallExpr of loc * string * type_expr list * pat list * pat list * func_binding(* oproep van functie/methode/lemma/fixpoint *)
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of loc * expr * switch_expr_clause list * (type_ list * type_) option ref
  | PredNameExpr of loc * string (* naam van predicaat en line of code*)
  | FuncNameExpr of string (*function name *)
  | CastExpr of loc * type_expr * expr (* cast *)
  | SizeofExpr of loc * type_expr
  | AddressOf of loc * expr
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
  | Package
and
  package =
    PackageDecl of loc * string * import list* decl list
and
  import =
    Import of loc * string * string option (* None betekent heel package, Some string betekent 1 ding eruit*)
and
  stmt =
    PureStmt of loc * stmt (* oproep van pure function in ghost range*)
  | NonpureStmt of loc * bool (* allowed *) * stmt
  | Assign of loc * string * expr (* toekenning *)
  | DeclStmt of loc * type_expr * string * expr (* enkel declaratie *)
  | Write of loc * expr * fieldref * expr (*  overschrijven van huidige waarde*)
  | WriteDeref of loc * expr * expr (* write to a pointer dereference *)
  | CallStmt of loc * string * type_expr list * expr list * func_binding(* oproep regel-naam-argumenten*)
  | IfStmt of loc * expr * stmt list * stmt list (* if  regel-conditie-branch1-branch2  *)
  | SwitchStmt of loc * expr * switch_stmt_clause list (* switch over inductief type regel-expr- constructor)*)
  | Assert of loc * pred (* assert regel-predicate *)
  | Leak of loc * pred (* expliciet lekken van assertie, nuttig op einde van thread*)
  | Open of loc * string * pat list * pat list * pat option (* open van predicate regel-pred fam-pred naam-pattern list- ...*)
  | Close of loc * string * pat list * pat list * pat option
  | ReturnStmt of loc * expr option (*return regel-return value (optie) *)
  | WhileStmt of loc * expr * pred * stmt list * loc (* while regel-conditie-lus invariant- lus body - close brace location *)
  | BlockStmt of loc * stmt list (* blok met {}   regel-body *)
  | PerformActionStmt of loc * bool ref (* in non-pure context *) * string * pat list * loc * string * pat list * loc * string * expr list * bool (* atomic *) * stmt list * loc (* close brace of body *) * (loc * expr list) option * loc * string * expr list
  | SplitFractionStmt of loc * string * pat list * expr option (* split_fraction ... by ... *)
  | MergeFractionsStmt of loc * string * pat list (* merge_fraction ...*)
  | CreateBoxStmt of loc * string * string * expr list * (loc * string * string * expr list) list (* and_handle clauses *)
  | CreateHandleStmt of loc * string * string * expr
  | DisposeBoxStmt of loc * string * pat list * (loc * string * pat list) list (* and_handle clauses *)
  | LabelStmt of loc * string
  | GotoStmt of loc * string
  | InvariantStmt of loc * pred (* join point *)
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
  | CoefPred of loc * pat * pred (* fractional permission met coeff-predicate*)
and
  switch_pred_clause =
  | SwitchPredClause of loc * string * string list * prover_type option list option ref * pred (*  clauses bij switch  regel-cons-lijst v var in cons- body*)
and
  func_kind =
  | Regular
  | Fixpoint
  | Lemma
and
  meth =
  | Meth of loc * type_expr option * string * (type_expr * string) list * (pred * pred) option * stmt list option * func_binding * visibility
and
  meth_spec =
  | MethSpec of loc * type_expr option * string * (type_expr * string) list * (pred * pred) option* func_binding * visibility
and
  cons =
  | Cons of loc * (type_expr * string) list * (pred * pred) option * stmt list option * visibility
and
  decl =
    Struct of loc * string * field list option
  | Inductive of loc * string * string list * ctor list (* inductief data type regel-naam-type parameters-lijst van constructors*)
  | Class of loc * string * meth list * field list *cons list* string * string list(* laatste 2 strings zijn naam v superklasse en lijst van namen van interfaces*)
  | Interface of loc * string * meth_spec list
  | PredFamilyDecl of loc * string * int * type_expr list * int option (* (Some n) means the predicate is precise and the first n parameters are input parameters *)
  | PredFamilyInstanceDecl of loc * string * (loc * string) list * (type_expr * string) list * pred
  | PredCtorDecl of loc * string * (type_expr * string) list * (type_expr * string) list * pred
  | Func of loc * func_kind * string list * type_expr option * string * (type_expr * string) list * bool (* atomic *) * string option (* function type *)
    * (pred * pred) option * (stmt list * loc (* Close brace *)) option * func_binding * visibility
  (* functie met regel-soort-return type-naam- lijst van parameters - contract - body*)
  | FuncTypeDecl of loc * ghostness * type_expr option * string * (type_expr * string) list * (pred * pred)
  (* typedef met regel-return type-naam-parameter lijst - contract *)
  | BoxClassDecl of loc * string * (type_expr * string) list * pred * action_decl list * handle_pred_decl list
and (* shared box is deeltje ghost state, waarde kan enkel via actions gewijzigd worden, handle predicates geven info over de ghost state, zelfs als er geen eigendom over de box is*)
  action_decl =
  | ActionDecl of loc * string * (type_expr * string) list * expr * expr
and (* action, kan value van shared box wijzigen*)
  handle_pred_decl =
  | HandlePredDecl of loc * string * (type_expr * string) list * expr * preserved_by_clause list
and (* handle predicate geeft info over ghost state van shared box, zelfs als er geen volledige eigendom is vd box*)
  preserved_by_clause =
  | PreservedByClause of loc * string * string list * stmt list
and
  ghostness = Ghost | Real
and
  field =
  | Field of loc * ghostness * type_expr * string * func_binding* visibility(* veld met regel-type-naam*)
and
  ctor =
  | Ctor of loc * string * type_expr list (* constructor met regel-naam-lijst v types v args*)
and
  member = FieldMember of field | MethMember of meth | ConsMember of cons

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
let dummy_srcpos = (("<nowhere>", "prelude"), 0, 0)
  let dummy_loc = (dummy_srcpos, dummy_srcpos)
  
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
  | Var (l, x, _) -> l
  | IntLit (l, n, t) -> l
  | StringLit (l, s) -> l
  | ClassLit (l, s) -> l
  | Operation (l, op, es, ts) -> l
  | Read (l, e, f) -> l
  | Deref (l, e, t) -> l
  | CallExpr (l, g, targs, pats0, pats,_) -> l
  | IfExpr (l, e1, e2, e3) -> l
  | SwitchExpr (l, e, secs, _) -> l
  | SizeofExpr (l, t) -> l
  | PredNameExpr (l, g) -> l
  | CastExpr (l, te, e) -> l
  | AddressOf (l, e) -> l

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
  | NonpureStmt (l, _, _) -> l
  | Assign (l, _, _) -> l
  | DeclStmt (l, _, _, _) -> l
  | Write (l, _, _, _) -> l
  | WriteDeref (l, _, _) -> l
  | CallStmt (l, _, _, _, _) -> l
  | IfStmt (l, _, _, _) -> l
  | SwitchStmt (l, _, _) -> l
  | Assert (l, _) -> l
  | Leak (l, _) -> l
  | Open (l, _, _, _, coef) -> l
  | Close (l, _, _, _, coef) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _, _) -> l
  | BlockStmt (l, ss) -> l
  | PerformActionStmt (l, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> l
  | SplitFractionStmt (l, _, _, _) -> l
  | MergeFractionsStmt (l, _, _) -> l
  | CreateBoxStmt (l, _, _, _, _) -> l
  | CreateHandleStmt (l, _, _, _) -> l
  | DisposeBoxStmt (l, _, _, _) -> l
  | LabelStmt (l, _) -> l
  | GotoStmt (l, _) -> l
  | InvariantStmt (l, _) -> l

let type_expr_loc t =
  match t with
    ManifestTypeExpr (l, t) -> l
  | StructTypeExpr (l, sn) -> l
  | IdentTypeExpr (l, x) -> l
  | ConstructedTypeExpr (l, x, targs) -> l
  | PtrTypeExpr (l, te) -> l
  | ArrayTypeExpr(l,te) -> l
  | PredTypeExpr(l,te) ->l
  
let veri_keywords= ["predicate";"requires";"|->"; "&*&"; "inductive";"fixpoint"; "switch"; "case"; ":";"return";
  "ensures";"close";"void"; "lemma";"open"; "if"; "else"; "emp"; "while"; "!="; "invariant"; "<"; ">"; "<="; ">="; "&&"; "++"; "--"; "+="; "-=";
  "||"; "forall"; "_"; "@*/"; "!";"predicate_family"; "predicate_family_instance";"predicate_ctor";"assert";"leak"; "@"; "["; "]";"{";
  "}";";"; "int";"true"; "false";"("; ")"; ",";"="; "|";"+"; "-"; "=="; "?";
  "box_class"; "action"; "handle_predicate"; "preserved_by"; "consuming_box_predicate"; "consuming_handle_predicate"; "perform_action"; "atomic";
  "create_box"; "and_handle"; "create_handle"; "dispose_box";
  "producing_box_predicate"; "producing_handle_predicate"; "box"; "handle"; "any"; "*"; "/"; "real"; "split_fraction"; "by"; "merge_fractions"
]
let c_keywords= ["struct"; "bool"; "char";"->";"sizeof";"typedef"; "#"; "include"; "ifndef";
  "define"; "endif"; "&"; "goto"
]
let java_keywords= ["public";"char";"private";"protected" ;"class" ; "." ; "static" ; "boolean";"new";"null";"interface";"implements";"package";"import";"*";"extends"
]

let file_type path=
  begin
  if Filename.check_suffix (Filename.basename path) ".c" then C
  else if Filename.check_suffix (Filename.basename path) ".jarsrc" then Java
  else if Filename.check_suffix (Filename.basename path) ".jarspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".java" then Java
  else if Filename.check_suffix (Filename.basename path) ".javaspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".scala" then Java
  else if Filename.check_suffix (Filename.basename path) ".h" then Header
  else failwith ("unknown extension")
  end
let opt p = parser [< v = p >] -> Some v | [< >] -> None
let rec comma_rep p = parser [< '(_, Kwd ","); v = p; vs = comma_rep p >] -> v::vs | [< >] -> []
let rep_comma p = parser [< v = p; vs = comma_rep p >] -> v::vs | [< >] -> []
let rec rep p = parser [< v = p; vs = rep p >] -> v::vs | [< >] -> []
let parse_angle_brackets (_, sp) p =
  parser [< '((sp', _), Kwd "<") when sp = sp'; v = p; '(_, Kwd ">") >] -> v

type spec_clause =
  AtomicClause
| FuncTypeClause of string
| RequiresClause of pred
| EnsuresClause of pred
  
module Scala = struct

let keywords = ["def"; "var"; "class"; "object"; "."; "new"; "null"; "package"; "import"; "extends"]

let rec
  parse_decl = parser
    [< '(l, Kwd "object"); '(_, Ident cn); '(_, Kwd "{"); ms = rep parse_method; '(_, Kwd "}") >] ->
    Class (l, cn, ms, [], [], "Object", [])
and
  parse_method = parser
    [< '(l, Kwd "def"); '(_, Ident mn); ps = parse_paramlist; t = parse_type_ann; co = parse_contract; '(_, Kwd "="); ss = parse_block >] ->
    let rt = match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t in
    Meth (l, rt, mn, ps, Some co, Some ss, Static, Public)
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
      | (_, []) -> IdentTypeExpr (l, tn)
      | _ -> raise (ParseException (l, "Type arguments are not supported."))
    end
and
  parse_targlist = parser
    [< '(_, Kwd "["); ts = rep_comma parse_type; '(_, Kwd "]") >] -> ts
  | [< >] -> []
and
  parse_contract = parser
    [< '(_, Kwd "/*@"); '(_, Kwd "requires"); pre = parse_asn; '(_, Kwd "@*/");
       '(_, Kwd "/*@"); '(_, Kwd "ensures"); post = parse_asn; '(_, Kwd "@*/") >] -> (pre, post)
and
  parse_asn = parser
    [< '(_, Kwd "("); a = parse_asn; '(_, Kwd ")") >] -> a
  | [< e = parse_expr >] -> ExprPred (expr_loc e, e)
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
  parse_block = parser
    [< '(_, Kwd "{"); ss = rep parse_stmt; '(_, Kwd "}") >] -> ss
and
  parse_stmt = parser
    [< '(l, Kwd "var"); '(_, Ident x); t = parse_type_ann; '(_, Kwd "="); e = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, t, x, e)
  | [< '(l, Kwd "assert"); a = parse_asn; '(_, Kwd ";") >] -> Assert (l, a)

end

let parse_decls =
let rec
  parse_decls = parser
[< '((p1, _), Kwd "/*@"); ds = parse_pure_decls; '((_, p2), Kwd "@*/"); ds' = parse_decls >] -> ds @ ds'
| [< '(l, Kwd "public");ds'=parser
    [<'(_, Kwd "class");'(_, Ident s);super=parse_super_class;il=parse_interfaces; mem=parse_java_members s;ds=parse_decls>]->Class(l,s,methods s mem,fields mem,constr mem,super,il)::ds
  | [<'(l, Kwd "interface");'(_, Ident cn);'(_, Kwd "{");mem=parse_interface_members cn;ds=parse_decls>]->
Interface(l,cn,mem)::ds
  >]-> ds'
| [<'(l, Kwd "interface");'(_, Ident cn);'(_, Kwd "{");mem=parse_interface_members cn;ds=parse_decls>]->
Interface(l,cn,mem)::ds (* TODO: enkel public classes/interfaces toelaten??*)
| [< '(l, Kwd "class");'(_, Ident s);super=parse_super_class;il=parse_interfaces; mem=parse_java_members s;ds=parse_decls>]->Class(l,s,methods s mem,fields mem,constr mem,super,il)::ds
| [< ds0 = parse_decl; ds = parse_decls >] -> ds0@ds
| [< >] -> []
and
  parse_super_class= parser
  [<'(_, Kwd "extends");'(_, Ident s)>] -> s
| [<>] -> "Object"
and
  parse_interfaces= parser
  [< '(_, Kwd "implements"); is = rep_comma (parser 
    [< '(l, Ident i); e=parser
      [<>]->(i)>] -> e); '(_, Kwd "{") >] -> is
| [<'(_, Kwd "{")>]-> []
and
  methods cn m=
  match m with
    MethMember (Meth (l, t, n, ps, co, ss,s,v))::ms -> Meth (l, t, n, ps, co, ss,s,v)::(methods cn ms)
    |_::ms -> methods cn ms
    | []->[]
and
  fields m=
  match m with
    FieldMember (Field (l, gh, t, f,fb,v))::ms -> Field (l, gh, t, f,fb,v)::(fields ms)
    |_::ms -> fields ms
    | []->[]
and
  constr m=
  match m with
    ConsMember(Cons(l,ps,co,ss,v))::ms -> Cons(l,ps,co,ss,v)::(constr ms)
    |_::ms -> constr ms
    | []->[]
and
  parse_interface_visibility = parser
  [<'(_, Kwd "public")>] -> Public
| [<>] -> Public
and
  parse_interface_members cn=parser
  [<'(_, Kwd "}")>] -> []
| [<v=parse_interface_visibility;m=parse_interface_meth v cn;mr=parse_interface_members cn>] -> m::mr
and
  parse_interface_meth vis cn= parser
[< t=parse_return_type;'(l,Ident f);ps = parse_paramlist;'(_, Kwd ";");co = opt parse_spec>]
    -> MethSpec(l,t,f,(IdentTypeExpr(l,cn),"this")::ps,co,Instance,vis)
and
  parse_visibility = parser
  [<'(_, Kwd "public")>] -> Public
| [<'(_, Kwd "private")>] -> Private
| [<'(_, Kwd "protected")>] -> Protected
| [<>] -> Package
and
  parse_java_members cn= parser
  [<'(_, Kwd "}")>] -> []
| [<v=parse_visibility;m=parse_java_member v cn;mr=parse_java_members cn>] -> m::mr
and
  parse_java_member vis cn= parser
  [< '(l, Kwd "static");t=parse_return_type;'(_,Ident n);
    ps = parse_paramlist;co = opt parse_spec; ss = parse_some_block>] -> MethMember(Meth(l,t,n,ps,co,ss,Static,vis))
| [<'(l,Ident t);e=parser
    [<'(_,Ident f);r=parser
      [<'(_, Kwd ";")>]->FieldMember(Field (l,Real,IdentTypeExpr(l,t),f,Instance,vis))
    | [< ps = parse_paramlist;(ss,co)=parser
        [<'(_, Kwd ";");co = opt parse_spec>]-> (None,co)
      | [<co = opt parse_spec; ss = parse_block>] -> (Some ss,co)
    >] -> MethMember(Meth(l,Some (IdentTypeExpr(l,t)),f,(IdentTypeExpr(l,cn),"this")::ps,co,ss,Instance,vis))
    >] -> r
  | [< ps = parse_paramlist;i=parser
      [<'(_, Kwd ";");co = opt parse_spec>]-> ConsMember(Cons(l,ps,co,None,vis))
    | [<co = opt parse_spec; ss = parse_block>]-> ConsMember(Cons(l,ps,co,Some ss,vis))
   >]-> i
 >] -> e
| [< t=parse_return_type;'(l,Ident f);r=parser
    [<'(_, Kwd ";")>] ->
      (match t with 
        None -> raise (ParseException (l, "Invalid type of field")) 
      | Some t -> FieldMember(Field (l,Real,t,f,Instance,vis)))
  | [< ps = parse_paramlist;(ss,co)=parser
      [<'(_, Kwd ";");co = opt parse_spec>]-> (None,co)
    | [<co = opt parse_spec; ss = parse_block>] -> (Some ss,co)
    >] -> 
      MethMember(Meth(l,t,f,(IdentTypeExpr(l,cn),"this")::ps,co,ss,Instance,vis))
>] -> r
and
  parse_decl = parser
  [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, Some fs)
  | [< '(_, Kwd ";") >] -> Struct (l, s, None)
  | [< t = parse_type_suffix (StructTypeExpr (l, s)); d = parse_func_rest Regular (Some t) >] -> d
  >] -> [d]
| [< '(l, Kwd "typedef"); rt = parse_return_type; '(_, Ident g); ps = parse_paramlist; '(_, Kwd ";"); c = parse_spec >] ->
  [FuncTypeDecl (l, Real, rt, g, ps, c)]
| [< t = parse_return_type; d = parse_func_rest Regular t >] -> [d]
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
  parse_pure_decl = parser
    [< '(l, Kwd "inductive"); '(li, Ident i); tparams = parse_type_params li; '(_, Kwd "="); cs = (parser [< cs = parse_ctors >] -> cs | [< cs = parse_ctors_suffix >] -> cs); '(_, Kwd ";") >] -> [Inductive (l, i, tparams, cs)]
  | [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> [d]
  | [< '(l, Kwd "predicate"); '(_, Ident g); '(_, Kwd "("); ps = rep_comma parse_param;
     (ps, inputParamCount) = (parser [< '(_, Kwd ";"); ps' = rep_comma parse_param >] -> (ps @ ps', Some (List.length ps)) | [< >] -> (ps, None));
     '(_, Kwd ")");
     body = (parser
       [< '(_, Kwd "requires"); p = parse_pred >] -> Some p
     | [< '(_, Kwd "="); p = parse_pred >] -> Some p
     | [< >] -> None); '(_, Kwd ";");
  >] -> [PredFamilyDecl (l, g, 0, List.map (fun (t, p) -> t) ps, inputParamCount)] @ (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, [], ps, body)])
  | [< '(l, Kwd "predicate_family"); '(_, Ident g); is = parse_paramlist; ps = parse_paramlist; '(_, Kwd ";") >]
  -> [PredFamilyDecl (l, g, List.length is, List.map (fun (t, p) -> t) ps, None)]
  | [< '(l, Kwd "predicate_family_instance"); '(_, Ident g); is = parse_index_list; ps = parse_paramlist;
     _ = (parser [< '(_, Kwd "requires") >] -> () | [< '(_, Kwd "=") >] -> ()); p = parse_pred; '(_, Kwd ";"); >] -> [PredFamilyInstanceDecl (l, g, is, ps, p)]
  | [< '(l, Kwd "predicate_ctor"); '(_, Ident g); ps1 = parse_paramlist; ps2 = parse_paramlist;
     '(_, Kwd "requires"); p = parse_pred; '(_, Kwd ";"); >] -> [PredCtorDecl (l, g, ps1, ps2, p)]
  | [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest Lemma t >] -> [d]
  | [< '(l, Kwd "box_class"); '(_, Ident bcn); ps = parse_paramlist;
       '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";");
       ads = parse_action_decls; hpds = parse_handle_pred_decls; '(_, Kwd "}") >] -> [BoxClassDecl (l, bcn, ps, inv, ads, hpds)]
  | [< '(l, Kwd "typedef"); '(_, Kwd "lemma"); rt = parse_return_type; '(_, Ident g); ps = parse_paramlist; '(_, Kwd ";"); c = parse_spec >] ->
    [FuncTypeDecl (l, Ghost, rt, g, ps, c)]
and
  parse_action_decls = parser
  [< ad = parse_action_decl; ads = parse_action_decls >] -> ad::ads
| [< >] -> []
and
  parse_action_decl = parser
  [< '(l, Kwd "action"); '(_, Ident an); ps = parse_paramlist; '(_, Kwd ";");
     '(_, Kwd "requires"); pre = parse_expr; '(_, Kwd ";");
     '(_, Kwd "ensures"); post = parse_expr; '(_, Kwd ";") >] -> ActionDecl (l, an, ps, pre, post)
and
  parse_handle_pred_decls = parser
  [< hpd = parse_handle_pred_decl; hpds = parse_handle_pred_decls >] -> hpd::hpds
| [< >] -> []
and
  parse_handle_pred_decl = parser
  [< '(l, Kwd "handle_predicate"); '(_, Ident hpn); ps = parse_paramlist;
     '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_expr; '(_, Kwd ";"); pbcs = parse_preserved_by_clauses; '(_, Kwd "}") >]
     -> HandlePredDecl (l, hpn, ps, inv, pbcs)
and
  parse_preserved_by_clauses = parser
  [< pbc = parse_preserved_by_clause; pbcs = parse_preserved_by_clauses >] -> pbc::pbcs
| [< >] -> []
and
  parse_preserved_by_clause = parser
  [< '(l, Kwd "preserved_by"); '(_, Ident an); '(_, Kwd "("); xs = rep_comma (parser [< '(_, Ident x) >] -> x); '(_, Kwd ")");
     ss = parse_block >] -> PreservedByClause (l, an, xs, ss)
and
  parse_func_rest k t = parser
  [< '(l, Ident g); tparams = parse_type_params l; ps = parse_paramlist; f =
    (parser
       [< '(_, Kwd ";"); (atomic, ft, co) = parse_spec_clauses >] -> Func (l, k, tparams, t, g, ps, atomic, ft, co, None,Static,Public)
     | [< (atomic, ft, co) = parse_spec_clauses;
          '(_, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >]
          -> 
          Func (l, k, tparams, t, g, ps, atomic, ft, co, Some (ss, closeBraceLoc), Static, Public)
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
| [< t = parse_type; _ = opt (parser [< '(_, Ident _) >] -> ()); ts = parse_more_types >] -> t::ts
and
  parse_more_types = parser
  [< '(_, Kwd ","); t = parse_type; _ = opt (parser [< '(_, Ident _) >] -> ()); ts = parse_more_types >] -> t::ts
| [< '(_, Kwd ")") >] -> []
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
  [< t = parse_type; '(l, Ident f); '(_, Kwd ";") >] -> Field (l, gh, t, f,Instance,Public)
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
| [< '(l, Kwd "real") >] -> ManifestTypeExpr (l, RealType)
| [< '(l, Kwd "bool") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "boolean") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "void") >] -> ManifestTypeExpr (l, Void)
| [< '(l, Kwd "char") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "predicate"); '(_, Kwd "("); ts = parse_types >] -> PredTypeExpr (l, ts)
| [< '(l, Kwd "box") >] -> ManifestTypeExpr (l, BoxIdType)
| [< '(l, Kwd "handle") >] -> ManifestTypeExpr (l, HandleIdType)
| [< '(l, Kwd "any") >] -> ManifestTypeExpr (l, AnyType)
| [< '(l, Ident n); targs = parse_type_args l >] -> if targs <> [] then ConstructedTypeExpr (l, n, targs) else IdentTypeExpr (l, n)
and
  parse_type_suffix t0 = parser
  [< '(l, Kwd "*"); t = parse_type_suffix (PtrTypeExpr (l, t0)) >] -> t
| [<'(l, Kwd "[");'(_, Kwd "]");>] -> ArrayTypeExpr(l,t0)
| [< >] -> t0
and
  parse_paramlist = parser [< '(_, Kwd "("); ps = rep_comma parse_param; '(_, Kwd ")") >] -> ps
and
  parse_param = parser
  [< t = parse_type; '(l, Ident pn) >] -> (t, pn)
and
  parse_pure_spec_clause = parser
  [< '(_, Kwd "atomic") >] -> AtomicClause
| [< '(_, Kwd ":"); '(_, Ident ft) >] -> FuncTypeClause ft
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
    let atomic = (parser [< 'AtomicClause >] -> out_count := !out_count + 1; true | [< >] -> false) clause_stream in
    let ft = (parser [< 'FuncTypeClause ft >] -> out_count := !out_count + 1; Some ft | [< >] -> None) clause_stream in
    let pre_post = (parser [< 'RequiresClause pre; 'EnsuresClause post >] -> out_count := !out_count + 2; Some (pre, post) | [< >] -> None) clause_stream in
    if !in_count > !out_count then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: atomic clause (optional), function type clause (optional), contract (optional).");
    (atomic, ft, pre_post)
and
  parse_spec = parser
    [< (atomic, ft, pre_post) = parse_spec_clauses >] ->
    match (atomic, ft, pre_post) with
      (false, None, None) -> raise Stream.Failure
    | (false, None, Some (pre, post)) -> (pre, post)
    | _ -> raise (Stream.Error "Incorrect kind, number, or order of specification clauses. Expected: requires clause, ensures clause.")
and
  parse_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> ss
and
  parse_some_block = parser
  [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> Some ss
| [<>] -> None
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
  parse_stmt0 =
  let assignment_stmt l lhs rhs =
    match lhs with
    | Var (_, x, _) -> Assign (l, x, rhs)
    | Read (_, e, f) -> Write (l, e, f, rhs)
    | Deref (_, e, _) -> WriteDeref (l, e, rhs)
    | _ -> raise (ParseException (expr_loc lhs, "The left-hand side of an assignment must be an identifier, a field dereference expression, or a pointer dereference expression."))
  in
  parser
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
     CallExpr (_, g, [], es1, es2,_) -> Open (l, g, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [< '(l, Kwd "close"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, [], es1, es2,_) -> Close (l, g, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of close statement must be call expression.")))
| [< '(l, Kwd "split_fraction"); '(_, Ident p); pats = parse_patlist;
     coefopt = (parser [< '(_, Kwd "by"); e = parse_expr >] -> Some e | [< >] -> None);
     '(_, Kwd ";") >] -> SplitFractionStmt (l, p, pats, coefopt)
| [< '(l, Kwd "merge_fractions"); '(_, Ident p); pats = parse_patlist; '(_, Kwd ";") >] -> MergeFractionsStmt (l, p, pats)
| [< '(l, Kwd "dispose_box"); '(_, Ident bcn); pats = parse_patlist;
     handleClauses = rep (parser [< '(l, Kwd "and_handle"); '(_, Ident hpn); pats = parse_patlist >] -> (l, hpn, pats));
     '(_, Kwd ";") >] -> DisposeBoxStmt (l, bcn, pats, handleClauses)
| [< '(l, Kwd "create_box"); '(_, Ident x); '(_, Kwd "="); '(_, Ident bcn); args = parse_arglist;
     handleClauses = rep (parser [< '(l, Kwd "and_handle"); '(_, Ident x); '(_, Kwd "="); '(_, Ident hpn); args = parse_arglist >] -> (l, x, hpn, args));
     '(_, Kwd ";")
     >] -> CreateBoxStmt (l, x, bcn, args, handleClauses)
| [< '(l, Kwd "goto"); '(_, Ident lbl); '(_, Kwd ";") >] -> GotoStmt (l, lbl)
| [< '(l, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";") >] -> InvariantStmt (l, inv)
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     '((sp1, _), Kwd "/*@"); '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '((_, sp2), Kwd "@*/");
     '(_, Kwd "{"); b = parse_stmts; '(closeBraceLoc, Kwd "}") >] -> WhileStmt (l, e, p, b, closeBraceLoc)
| [< '(l, Kwd "{"); ss = parse_stmts; '(_, Kwd "}") >] -> BlockStmt (l, ss)
| [< '(lcb, Kwd "consuming_box_predicate"); '(_, Ident pre_bpn); pre_bp_args = parse_patlist;
     '(lch, Kwd "consuming_handle_predicate"); '(_, Ident pre_hpn); pre_hp_args = parse_patlist;
     '(lpa, Kwd "perform_action"); '(_, Ident an); aargs = parse_arglist; atomic = (parser [< '(_, Kwd "atomic") >] -> true | [< >] -> false);
     '(_, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}");
     post_bp_args =
       opt
         begin
           parser
             [< '(lpb, Kwd "producing_box_predicate"); '(_, Ident post_bpn); post_bp_args = parse_arglist >] ->
             if post_bpn <> pre_bpn then raise (ParseException (lpb, "The box predicate name cannot change."));
             (lpb, post_bp_args)
         end;
     '(lph, Kwd "producing_handle_predicate"); '(_, Ident post_hpn); post_hp_args = parse_arglist;
     '(_, Kwd ";") >] ->
     begin
       match (atomic, post_bp_args) with
       | (true, Some (lpb, _)) -> raise (ParseException (lpb, "An atomic perform_action statement must not include a producing_box_predicate clause."))
       | _ -> ()
     end;
     PerformActionStmt (lcb, ref false, pre_bpn, pre_bp_args, lch, pre_hpn, pre_hp_args, lpa, an, aargs, atomic, ss, closeBraceLoc, post_bp_args, lph, post_hpn, post_hp_args)
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] -> (match e with CallExpr (l, g, targs, [], es,fb) -> CallStmt (l, g, targs, List.map (function LitPat e -> e) es,fb) | _ -> raise (ParseException (expr_loc e, "An expression used as a statement must be a call expression.")))
  | [< '(l, Kwd ":") >] -> (match e with Var (_, lbl, _) -> LabelStmt (l, lbl) | _ -> raise (ParseException (l, "Label must be identifier.")))
  | [< '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] -> assignment_stmt l e rhs
  | [< '(l, Kwd "++"); '(_, Kwd ";") >] -> assignment_stmt l e (Operation (l, Add, [e; IntLit (l, unit_big_int, ref None)], ref None))
  | [< '(l, Kwd "--"); '(_, Kwd ";") >] -> assignment_stmt l e (Operation (l, Sub, [e; IntLit (l, unit_big_int, ref None)], ref None))
  | [< '(l, Kwd "+="); e' = parse_expr; '(_, Kwd ";") >] -> assignment_stmt l e (Operation (l, Add, [e; e'], ref None))
  | [< '(l, Kwd "-="); e' = parse_expr; '(_, Kwd ";") >] -> assignment_stmt l e (Operation (l, Sub, [e; e'], ref None))
  | [<'(_, Ident x); '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >]->
    (match e with
     | Var (lx, t, _) -> DeclStmt (l, IdentTypeExpr (lx,t), x, rhs)
     | _ -> raise (ParseException (expr_loc e, "Parse error."))
    )
  >] -> s
| [< te = parse_type; '(_, Ident x); '(l, Kwd "=");
     s = parser
       [< '(l, Kwd "create_handle"); '(_, Ident hpn); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] ->
         begin
           match te with ManifestTypeExpr (_, HandleIdType) -> () | _ -> raise (ParseException (l, "Target variable of handle creation statement must have type 'handle'."))
         end;
         CreateHandleStmt (l, x, hpn, e)
     | [< rhs = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, te, x, rhs)
  >] -> s
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
     | CallExpr (l, g, [], pats0, pats,_) -> CallPred (l, new predref g, pats0, pats)
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
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); p = parse_pred; '(_, Kwd ";") >] -> SwitchPredClause (l, c, pats, ref None, p)
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
  parse_expr_primary = parser
  [< '(l, Kwd "true") >] -> True l
| [< '(l, Kwd "false") >] -> False l
| [< '(l, Kwd "null") >] -> Null l
| [< '(l, Kwd "new");'(_, Ident x);args0 = parse_patlist;>] -> CallExpr(l,("new "^x),[],[],args0,Static)
| [<
    '(l, Ident x);
    targs = parse_type_args l;
    ex = parser
      [<
        args0 = parse_patlist;
        e = parser
          [< args = parse_patlist >] -> CallExpr (l, x, targs, args0, args,Static)
        | [< >] -> CallExpr (l, x, targs, [], args0,Static)
      >] -> e
    | [<
        '(l, Kwd ".") when targs = [];
        r = parser
          [<'(l, Kwd "class")>] -> ClassLit(l,x)
        | [<
            '(l, Ident f);
            e = parser
              [<args0 = parse_patlist>] -> CallExpr (l, f, [], [], LitPat(Var(l,x,ref None))::args0,Instance)
            | [<>] -> Read (l, Var(l,x, ref None), new fieldref f)
          >]->e 
      >]-> r
    | [< >] -> if targs = [] then Var (l, x, ref None) else CallExpr (l, x, targs, [], [], Static)
  >] -> ex
| [< '(l, Int i) >] -> IntLit (l, i, ref None)
| [< '(l, String s) >] -> StringLit (l, s)
| [< '(l, Kwd "(");
     e = parser
     [< e0 = parse_expr; '(_, Kwd ")");
         e = parser
           [< '(l', Ident y) >] -> (match e0 with 
             Var (lt, x, _) ->CastExpr (l, IdentTypeExpr (lt, x), Var (l', y, ref (Some LocalVar)))
           | _ -> raise (ParseException (l, "Type expression of cast expression must be identifier: ")))
         | [<>] -> e0
     >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e
(*
| [< '(l, Kwd "(");
     e = parser
     [< e = parse_expr; '(_, Kwd ")") >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e*)
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses; '(_, Kwd "}") >] -> SwitchExpr (l, e, cs, ref None)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "!"); e = parse_expr_primary >] -> Operation(l, Not, [e], ref None)
| [< '(l, Kwd "@"); '(_, Ident g) >] -> PredNameExpr (l, g)
| [< '(l, Kwd "*"); e = parse_expr_suffix >] -> Deref (l, e, ref None)
| [< '(l, Kwd "&"); e = parse_expr_suffix >] -> AddressOf (l, e)
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
  parse_expr_mul_rest e0 = parser
  [< '(l, Kwd "*"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Mul, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "/"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Div, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_arith_rest e0 = parser
  [< '(l, Kwd "+"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Add, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "-"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_rel_rest e0 = parser
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Lt, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd ">"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Lt, [e1; e0], ref None)) >] -> e
| [< '(l, Kwd ">="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e1; e0], ref None)) >] -> e
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
  parse_decls

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
  
let rec parse_imports= parser
  [<'(l, Kwd "import");n= parse_import_name;rest=parse_imports>] -> let (pn,el)=n in Import(l,pn,el)::rest
| [<>]-> []

let parse_ghost_import_list= parser
  [< '(_, Kwd "/*@"); is=parse_imports; '(_, Kwd "@*/")>] -> is
| [<>]->[]

let rec parse_non_ghost_import_list= parser
  [< is=parse_imports>]->is
| [<>]-> []

let parse_package_decl= parser
  [< (l,p) = parse_package; i=parse_ghost_import_list;i'=parse_non_ghost_import_list; ds=parse_decls;>] -> PackageDecl(l,p,Import(dummy_loc,"java.lang",None)::(i@i'),ds)

let parse_scala_file path reportRange =
  let lexer = make_lexer (veri_keywords@Scala.keywords) in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (streamSource path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< ds = rep Scala.parse_decl; _ = Stream.empty >] -> PackageDecl(dummy_loc,"",[Import(dummy_loc,"java.lang",None)],ds) in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_java_file path reportRange=
  if Filename.check_suffix (Filename.basename path) ".scala" then
    parse_scala_file path reportRange
  else
  let lexer = make_lexer (veri_keywords@java_keywords) in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (streamSource path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< p = parse_package_decl; _ = Stream.empty >] -> p in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_include_directives ignore_eol =
  let rec parse_include_directives = parser
    [< header = parse_include_directive; headers = parse_include_directives >] -> header::headers
  | [< >] -> []
  and
  parse_include_directive = parser
  [< '(_, Kwd "#"); _ = (fun _ -> ignore_eol := false); '(_, Kwd "include"); '(l, String header); '(_, Eol) >] -> ignore_eol := true; (l, header)
in
  parse_include_directives

let parse_c_file path reportRange reportShouldFail =
  let lexer = make_lexer (veri_keywords@c_keywords) in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (streamSource path) reportRange reportShouldFail in
  let parse_c_file =
    parser
      [< headers = parse_include_directives ignore_eol; ds = parse_decls; _ = Stream.empty >] -> (headers,
[PackageDecl(dummy_loc,"",[],ds)])
  in
  try
    parse_c_file token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_header_file basePath relPath reportRange reportShouldFail =
  let lexer = make_lexer (veri_keywords@c_keywords) in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (streamSource (Filename.concat basePath relPath)) reportRange reportShouldFail in
  let parse_header_file =
    parser
      [< '(_, Kwd "#"); _ = (fun _ -> ignore_eol := false); '(_, Kwd "ifndef"); '(_, PreprocessorSymbol x); '(_, Eol);
         '(_, Kwd "#"); '(_,Kwd "define"); '(lx', PreprocessorSymbol x'); '(_, Eol); _ = (fun _ -> ignore_eol := true);
         headers = parse_include_directives ignore_eol; ds = parse_decls;
         '(_, Kwd "#"); _ = (fun _ -> ignore_eol := false); '(_, Kwd "endif"); _ = (fun _ -> ignore_eol := true);
         _ = Stream.empty >] ->
      if x <> x' then raise (ParseException (lx', "Malformed header file prelude: preprocessor symbols do not match."));
      (headers, [PackageDecl(dummy_loc,"",[],ds)])
  in
  try
    parse_header_file token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let rec parse_jarspec_file basePath relPath reportRange =
  let lexer = make_lexer ["."] in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (streamSource (Filename.concat basePath relPath)) reportRange (fun _ -> ()) in
  let rec parse_file=
    parser
      [< '(l, Ident fname);'(_, Kwd ".");'(_, Ident extension);e= parse_file>] ->
        if extension="jar" then
          match (parse_jarspec_file basePath (fname^".jarspec") reportRange) with
          (_,allspecs') -> (match e with (jarspecs,allspecs) -> (jarspecs,allspecs@allspecs'))
        else
          if extension <> "javaspec" then 
            raise (ParseException (l, "Only javaspec or jar files can be specified here."))
          else
            let filename=fname^".javaspec" in (match e with (jarspecs,allspecs) -> (filename::jarspecs,filename::allspecs))
    | [< _ = Stream.empty>] -> ([],[])
  in
  try
    parse_file token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))  

let rec parse_main_class= parser
  [<'(l, Ident fname); e=parser
    [<'(_, Kwd ".");(r,_)=parse_main_class>] -> (fname^"."^r,l)
  | [<>] -> (fname,l)
  >] -> e
  
let rec parse_jarsrc_file basePath relPath reportRange =
  let lexer = make_lexer [".";"-"] in
  let streamSource path = Stream.of_string (readFile path) in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (streamSource (Filename.concat basePath relPath)) reportRange (fun _ -> ()) in
  let main=ref ("",dummy_loc) in
  let rec parse_file =
    parser
      [< '(l, Ident fname);z= parser
        [<'(_, Kwd ".");'(_, Ident extension);e= parse_file>] ->
        if extension="jar" then
          match (parse_jarspec_file basePath (fname^".jarspec") reportRange) with
          (jarspecs,allspecs)->(match e with (implist,jarlist,jdepds) -> (jarspecs@implist,(List.map (fun n -> (l,n))allspecs)@jarlist,(fname^"."^extension)::jdepds))
        else
          if extension <> "java" then 
            raise (ParseException (l, "Only java or jar files can be specified here."))
          else
            (match e with (implist,jarlist,jdepds) -> ((fname^".java")::implist,jarlist,jdepds))
      | [<'(_, Kwd "-");'(_, Ident cls);(main_class,lm)=parse_main_class;e= parse_file>] ->
        if fname="main" && cls="class" then
          begin
          if !main<>("",dummy_loc) then
            raise (ParseException (lm, "There can only be one main method"))
          else
            main:=(main_class,lm);e
          end
        else
         raise (ParseException (l, "The class containing the main method should be specified as: main-class ClassName"))
      >] -> z
    | [< _ = Stream.empty>] -> ([],[],[])
  in
  try
    match parse_file token_stream with (implist,jarlist,jdepds) ->(!main,implist,jarlist,jdepds)
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  
let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

exception StaticError of loc * string

let static_error l msg = raise (StaticError (l, msg))

type 'termnode heap = (('termnode * bool) * 'termnode * 'termnode list * int option) list
type 'termnode env = (string * 'termnode) list
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext

let string_of_chunk ((g, literal), coef, ts, size) = (if coef = "1" then "" else "[" ^ coef ^ "]") ^ g ^ "(" ^ String.concat ", " ts ^ ")"

let string_of_heap h = String.concat " * " (List.map string_of_chunk h)

let string_of_context c =
  match c with
    Assuming t -> "Assuming " ^ t
  | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s
  | PushSubcontext -> "Entering subcontext"
  | PopSubcontext -> "Leaving subcontext"

exception SymbolicExecutionError of string context list * string * loc * string

let full_name pn n=
  if pn="" then n 
  else if startswith n (pn^".") then n
       else (pn^"."^n)

let zip xs ys =
  let rec iter xs ys zs =
    match (xs, ys) with
      ([], []) -> Some (List.rev zs)
    | (x::xs, y::ys) -> iter xs ys ((x, y)::zs)
    | _ -> None
  in
  iter xs ys []

let unzip xs=
  let rec iter xs ys=
    match xs with
      [] -> Some (List.rev ys)
    | (x, y)::rest -> iter rest ((x,y)::ys)
    | _ -> None
  in
  iter xs []
  
let do_finally tryBlock finallyBlock =
  let result =
    try
      tryBlock()
    with e -> finallyBlock(); raise e
  in
  finallyBlock();
  result

type options = {option_verbose: bool; option_disable_overflow_check: bool; option_allow_should_fail: bool; option_emit_manifest: bool}

let verify_program_core (ctxt: ('typenode, 'symbol, 'termnode) Proverapi.context) options path reportRange breakpoint =

  let {
    option_verbose=verbose;
    option_disable_overflow_check=disable_overflow_check;
    option_allow_should_fail=allow_should_fail;
    option_emit_manifest=emit_manifest
  } = options in
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
  
  let alloc_nullary_ctor j s = mk_symbol s [] ctxt#type_inductive (Proverapi.Ctor (CtorByOrdinal j)) in

  let get_class_symbol = mk_symbol "getClass" [ctxt#type_int] ctxt#type_int Uninterp in
  
  let boolt = Bool in
  let intt = IntType in

  let real_zero = ctxt#mk_reallit 0 in
  let real_unit = ctxt#mk_reallit 1 in
  let real_half = ctxt#mk_reallit_of_num (Num.div_num (Num.num_of_int 1) (Num.num_of_int 2)) in
  
  let min_int_big_int = big_int_of_string "-2147483648" in
  let min_int_term = ctxt#mk_intlit_of_string "-2147483648" in
  let max_int_big_int = big_int_of_string "2147483647" in
  let max_int_term = ctxt#mk_intlit_of_string "2147483647" in
  let max_ptr_big_int = big_int_of_string "4294967295" in
  let max_ptr_term = ctxt#mk_intlit_of_string "4294967295" in
  
  let real_unit_pat = LitPat (IntLit (dummy_loc, unit_big_int, ref (Some RealType))) in

  let programDir = Filename.dirname path in
  let preludePath = Filename.concat bindir "prelude.h" in
  let rtdir= Filename.concat bindir "rt" in 
  let rtpath= Filename.concat rtdir "rt.jarspec" in
  let shouldFailLocs = ref [] in
  
  let reportShouldFail l =
    if allow_should_fail then
      shouldFailLocs := l::!shouldFailLocs
    else
      static_error l "Should fail directives are not allowed; use the -allow_should_fail command-line option to allow them."
  in
  
  let check_should_fail default body =
    let locs_match ((path0, line0, _), _) ((path1, line1, _), _) = path0 = path1 && line0 = line1 in
    let should_fail l = List.exists (locs_match l) !shouldFailLocs in
    let has_failed l = shouldFailLocs := remove (locs_match l) !shouldFailLocs; default in
    try
      body ()
    with
    | StaticError (l, msg) when should_fail l -> has_failed l
    | SymbolicExecutionError (ctxts, phi, l, msg) when should_fail l -> has_failed l
  in
  
  let headermap = ref [] in
  let spec_classes= ref [] in
  let spec_lemmas= ref [] in
  let meths_impl= ref [] in
  let cons_impl= ref [] in
  let main_meth= ref [] in
  
  let extract_specs ps=
    let rec iter (pn,ilist) classes lemmas ds=
      match ds with
      [] -> (classes,lemmas)
    | Class(l,cn,meths,fds,cons,super,inames)::rest -> let cn=full_name pn cn in
      let meths'= List.filter (fun x-> match x with Meth(lm, t, n, ps, co, ss,fb,v) -> match ss with None->true |Some _ -> false) meths 
      in
      let cons'= List.filter (fun x-> match x with Cons (lm,ps,co,ss,v) -> match ss with None->true |Some _ -> false) cons 
      in
      iter (pn,ilist) (Class(l,cn,meths',fds,cons,super,inames)::classes) lemmas rest
    | Func(l,Lemma,tparams,rt,fn,arglist,atomic,ftype,contract,None,fb,vis) as elem ::rest->
      let fn=full_name pn fn in iter (pn,ilist) classes (elem::lemmas) rest
    | _::rest -> 
      iter (pn,ilist) classes lemmas rest
    in
    let rec iter' (classes,lemmas) ps=
      match ps with
        PackageDecl(l,pn,ilist,ds)::rest-> iter' (iter (pn,ilist) classes lemmas ds) rest
      | [] -> (classes,lemmas)
    in
    iter' ([],[]) ps
  in
  
  let rec check_file include_prelude basedir headers ps =
  let (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) =
    if include_prelude then
      if file_type path =Java then
      begin
      match try_assoc rtpath !headermap with
        None -> 
          let (_,allspecs)= parse_jarspec_file rtdir "rt.jarspec" reportRange in
          let ds = (List.map (fun x -> (parse_java_file (Filename.concat rtdir x) reportRange)) allspecs) in
          let (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0, _, _,boxmap0,classmap0,interfmap0) = check_file false bindir [] ds in
          headermap := (rtpath, ([], structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0))::!headermap;
          (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0)
      | Some ([], structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) ->
        (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0)
      end
      else
      begin
      match try_assoc preludePath !headermap with
        None ->
        let ([], ds) = parse_header_file bindir "prelude.h" reportRange reportShouldFail in
        let (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0, _, _,boxmap0,classmap0,interfmap0) = check_file false bindir [] ds in
        headermap := (preludePath, ([], structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0))::!headermap;
        (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0)
      | Some ([], structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) ->
        (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0)
      end
      else
      ([], [], [], [], [], [], [], [], [], [], [], [],[],[])
  in
  let append_nodups xys xys0 string_of_key l elementKind =
    let rec iter xys =
      match xys with
        [] -> xys0
      | ((x, y) as elem)::xys ->
        if List.mem_assoc x xys0 then static_error l ("Duplicate " ^ elementKind ^ " '" ^ string_of_key x ^ "'");
        elem::iter xys
    in
    iter xys
  in

  let id x = x in
  
  let (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) =
    let headers_included = ref [] in
    let rec iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers =
      match headers with
        [] -> (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0)
      | (l, header_path)::headers ->
    if file_type path <> Java then
        if List.mem header_path ["bool.h"; "assert.h"] then
          iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers
        else
        begin
          if Filename.basename header_path <> header_path then static_error l "Include path should not include directory.";
          let localpath = Filename.concat basedir header_path in
          let (basedir, relpath, path) =
            if Sys.file_exists localpath then
              (basedir, Filename.concat "." header_path, localpath)
            else
              let systempath = Filename.concat bindir header_path in
              if Sys.file_exists systempath then
                (bindir, header_path, systempath)
              else
                static_error l "No such file."
          in
          if List.mem path !headers_included then
            iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers
          else
          begin
            headers_included := path::!headers_included;
            let (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap) =
              match try_assoc path !headermap with
                None ->
                let (headers', ds) = parse_header_file basedir relpath reportRange reportShouldFail in
                let (structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap, _, _,boxmap,classmap,interfmap) = check_file true basedir headers' ds in
                headermap := (path, (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap))::!headermap;
                (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap)
              | Some (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap) ->
                (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap)
            in
            let (structmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) = iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers' in
            iter
              (append_nodups structmap structmap0 id l "struct")
              (append_nodups inductivemap inductivemap0 id l "inductive datatype")
              (append_nodups purefuncmap purefuncmap0 id l "pure function")
			  (append_nodups predctormap predctormap0 id l "predicate constructor")
              (append_nodups fixpointmap fixpointmap0 id l "fixpoint function")
              (malloc_block_pred_map @ malloc_block_pred_map0)
              (field_pred_map @ field_pred_map0)
              (append_nodups predfammap predfammap0 id l "predicate")
              (append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance")
              (append_nodups functypemap functypemap0 id l "function type")
              (append_nodups funcmap funcmap0 id l "function")
              (append_nodups boxmap boxmap0 id l "box predicate")
              (append_nodups classmap classmap0 id l "class")
              (append_nodups interfmap interfmap0 id l "interface")
              headers
          end
        end
    else (* JAVA DEEL*)
          begin
          let localpath = Filename.concat basedir header_path in
          let (basedir, relpath, path) =
            if Sys.file_exists localpath then
              (basedir, Filename.concat "." header_path, localpath)
            else
              let systempath = Filename.concat bindir header_path in
              if Sys.file_exists systempath then
                (bindir, header_path, systempath)
              else
                static_error l ("No such file: "^systempath)
          in
          if List.mem path !headers_included then
            iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers
          else
          if Filename.check_suffix path ".javaspec" then (* javaspec files van andere jar's*)
            begin
            headers_included := path::!headers_included;
            iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers
            end
          else (* laatste el v lijst v headers is path naar jarspec van eigen jar*)
          begin
            headers_included := path::!headers_included;
            let (jarspecs,allspecs)= parse_jarspec_file basedir relpath reportRange in
            let allspecs= remove (fun x -> List.mem x !headers_included)(list_remove_dups allspecs) in
            let (classes,lemmas)=extract_specs ((List.map (fun x -> (parse_java_file (Filename.concat basedir x) reportRange)) jarspecs))in
            let (headers',ds) = ([],(List.map (fun x -> (parse_java_file (Filename.concat basedir x) reportRange)) allspecs)) in
            let (structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap, _, _,boxmap,classmap,interfmap) = check_file true basedir [] ds in
            headermap := (path, (headers', structmap, inductivemap, purefuncmap,predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap,boxmap,classmap,interfmap))::!headermap;
            spec_classes:=classes;
            spec_lemmas:=lemmas;
            ((append_nodups structmap structmap0 id l "struct"),
            (append_nodups inductivemap inductivemap0 id l "inductive datatype"),
            (append_nodups purefuncmap purefuncmap0 id l "pure function"),
			(append_nodups predctormap predctormap0 id l "predicate constructor"),
            (append_nodups fixpointmap fixpointmap0 id l "fixpoint function"),
            (malloc_block_pred_map @ malloc_block_pred_map0),
            (field_pred_map @ field_pred_map0),
            (append_nodups predfammap predfammap0 id l "predicate"),
            (append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance"),
            (append_nodups functypemap functypemap0 id l "function type"),
            (append_nodups funcmap funcmap0 id l "function"),
            (append_nodups boxmap boxmap0 id l "box predicate"),
            (append_nodups classmap classmap0 id l "class"),
            (append_nodups interfmap interfmap0 id l "interface"))
          end
        end
    in
    iter structmap0 inductivemap0 purefuncmap0 predctormap0 fixpointmap0 malloc_block_pred_map0 field_pred_map0 predfammap0 predinstmap0 functypemap0 funcmap0 boxmap0 classmap0 interfmap0 headers
  in

  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds_opt)::ds ->
        begin
          match try_assoc sn structmap0 with
            Some (_, Some _) -> static_error l "Duplicate struct name."
          | Some (_, None) | None -> ()
        end;
        begin
          match try_assoc sn sdm with
            Some (_, Some _) -> static_error l "Duplicate struct name."
          | Some (_, None) | None -> iter ((sn, (l, fds_opt))::sdm) ds
        end
      | _::ds -> iter sdm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  in
    
  let functypenames = 
    let ds=match ps with
        [PackageDecl(_,"",[],ds)] -> ds
      | _ when file_type path=Java -> []
    in
    flatmap (function (FuncTypeDecl (_, gh, _, g, _, _)) -> [g] | _ -> []) ds
  in
  
  let inductivedeclmap=
    let rec iter pn idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, tparams, ctors))::ds -> let n=full_name pn i in
        if n = "bool" || n = "boolean" || n = "int" || List.mem_assoc n idm || List.mem_assoc n inductivemap0 then
          static_error l "Duplicate datatype name."
        else
          iter pn ((n, (l, tparams, ctors))::idm) ds
      | _::ds -> iter pn idm ds
    in
    let rec iter' idm ps=
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter pn idm ds) rest
      | [] -> idm
    in
    iter' [] ps
  in
  
  let rec try_assoc' (pn,imports) name map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> Some (List.assoc (full_name pn name) map)
    | _ when List.mem_assoc name map-> Some (List.assoc name map)
    | Import(l,p,None)::rest when List.mem_assoc (full_name p name) map->  Some (List.assoc (full_name p name) map)
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map-> Some (List.assoc (full_name p name) map) 
    | _::rest -> try_assoc' (pn,rest) name map
    | [] -> None
  in
  
  let rec try_assoc_pair' (pn,imports) (n,n') map=
    match imports with
      _ when List.mem_assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map -> Some (List.assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map)
    | _ when List.mem_assoc (n,n') map-> Some (List.assoc (n,n') map)
    | Import(l,p,None)::rest when List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map->  Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map)
    | Import(l,p,Some n2)::rest when n=n2 && List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map-> Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map) 
    | _::rest -> try_assoc_pair' (pn,rest) (n,n') map
    | [] -> None
  in

  let try_assoc2' (pn,imports)x xys1 xys2 =
    match try_assoc' (pn,imports) x xys1 with
      None -> try_assoc' (pn,imports) x xys2
    | result -> result
  in
  
  let rec search name (pn,imports) map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> true
    | _ when List.mem_assoc name map -> true
    | Import(l,p,None)::_ when List.mem_assoc (full_name p name) map-> true
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map-> true
    | _::rest -> search name (pn,rest) map
    | []->  false
  in
  
  let rec search' name (pn,imports) map=
    match imports with
      _ when List.mem_assoc name map-> Some name
    | _ when List.mem_assoc (full_name pn name) map -> Some (full_name pn name)
    | Import(l,p,None)::_ when List.mem_assoc (full_name p name) map-> Some (full_name p name)
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map ->Some (full_name p name)
    | _::rest -> search' name (pn,rest) map
    | [] -> None
  in
  
  let search2' x (pn,imports) xys1 xys2 =
    match search' x (pn,imports) xys1 with
      None -> search' x (pn,imports) xys2
    | result -> result
  in
  
  let (interfdeclmap,classdeclmap)=
    let rec iter (pn,il) ifdm classlist ds =
      match ds with
        [] -> (ifdm,classlist)
      | (Interface (l, i, meth_specs))::ds -> let i= full_name pn i in 
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i)
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i)
        else
         iter (pn,il) ((i, (l,meth_specs,pn,il))::ifdm) classlist ds
      | (Class (l, i, meths,fields,constr,super,interfs))::ds -> 
        let i= full_name pn i in
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i)
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i)
        else
          let _=
          if i<> "java.lang.Object" then
              let rec check_interfs ls=
                  match ls with
                    [] -> ()
                  | i::ls -> match search2' i (pn,il) ifdm interfmap0 with 
                              Some _ -> check_interfs ls
                            | None -> static_error l ("Interface wasn't found: "^i^" "^pn)
              in
              match search2' super (pn,il) classlist classmap0 with
                None-> static_error l ("Superclass wasn't found: "^super)
              | Some _ -> check_interfs interfs
          in
          iter (pn,il) ifdm ((i, (l,meths,fields,constr,super,interfs,pn,il))::classlist) ds
      | _::ds -> iter (pn,il) ifdm classlist ds
    in
    let rec iter' (ifdm,classlist) ps =
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter (pn,ilist) ifdm classlist ds) rest
      | [] -> (ifdm,classlist)
    in
    iter' ([],[]) ps
  in
  
  let classfmap =
    List.map
      (fun (sn, (l,meths, fds_opt,constr,super,interfs,pn,ilist)) ->
         let rec iter fmap fds =
           match fds with
             [] -> (sn, (l,meths, Some (List.rev fmap),constr,super,interfs,pn,ilist))
           | Field (lf, _, t, f,Instance,vis)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
                 | ManifestTypeExpr (_, Bool) -> Bool
                 | IdentTypeExpr(lt, sn) ->
                   match search2' sn (pn,ilist) classdeclmap classmap0 with
                     Some s -> ObjType s
                   | None -> match search2' sn (pn,ilist) interfdeclmap interfmap0 with
                       Some s -> ObjType s
                     | None -> static_error lt ("No such class or interface: "^sn)
                 | _ -> static_error (type_expr_loc te) "Invalid field type or field type component in class."
               in
               iter ((f, (lf, check_type t,vis))::fmap) fds
             )
         in
          begin
           match fds_opt with
             fds -> iter [] fds
           | [] -> (sn, (l,meths,None,constr,super,interfs,pn,ilist))
         end
      )
      classdeclmap
  in
  
  let inductive_arities =
    List.map (fun (i, (_, tparams, _)) -> (i, List.length tparams)) inductivedeclmap
    @ List.map (fun (i, (_, tparams, _)) -> (i, List.length tparams)) inductivemap0
  in
  
  let rec check_pure_type (pn,ilist) tpenv te=
    match te with
      ManifestTypeExpr (l, t) -> t
    | ArrayTypeExpr (l, t) -> check_pure_type (pn,ilist) tpenv t
    | IdentTypeExpr (l, id) ->
      if List.mem id tpenv then
        TypeParam id
      else
      begin
      match search' id (pn,ilist) inductive_arities with
        Some s -> let n=List.assoc s inductive_arities in
        if n > 0 then static_error l "Missing type arguments.";
        InductiveType (s, [])
      | None ->
        match (search2' id (pn,ilist) classdeclmap classmap0) with
          Some s -> ObjType s
        | None -> match (search2' id (pn,ilist) interfdeclmap interfmap0) with
                    Some s->ObjType s
                  | None ->
                    if List.mem id functypenames || List.mem_assoc id functypemap0 then
                      FuncType id
                    else
                      static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^pn^" "^id)
      end
    | ConstructedTypeExpr (l, id, targs) ->
      begin
      match try_assoc' (pn,ilist) id inductive_arities with
        Some n ->
        if n <> List.length targs then static_error l "Incorrect number of type arguments.";
        InductiveType (id, List.map (check_type_arg (pn,ilist) tpenv) targs)
      | None -> static_error l "No such inductive datatype."
      end
    | StructTypeExpr (l, sn) ->
      if not (List.mem_assoc sn structmap0 || List.mem_assoc sn structdeclmap) then
        static_error l "No such struct."
      else
        StructType sn
    | PtrTypeExpr (l, te) -> PtrType (check_pure_type (pn,ilist) tpenv te)
    | PredTypeExpr (l, tes) -> PredType (List.map (check_pure_type (pn,ilist) tpenv) tes )
  and check_type_arg (pn,ilist) tpenv te =
    let t = check_pure_type (pn,ilist) tpenv te in
    t
  in
  
  let rec instantiate_type tpenv t =
    if tpenv = [] then t else
    match t with
      TypeParam x -> List.assoc x tpenv
    | PtrType t -> PtrType (instantiate_type tpenv t)
    | InductiveType (i, targs) -> InductiveType (i, List.map (instantiate_type tpenv) targs)
    | PredType pts -> PredType (List.map (instantiate_type tpenv) pts)
    | _ -> t
  in
  
  let class_symbols = 
    (List.map (fun (c,_) -> (c, mk_symbol c [] ctxt#type_int Uninterp)) classdeclmap)@
    (List.map (fun (c,_) -> (c, mk_symbol c [] ctxt#type_int Uninterp)) interfdeclmap)@
    (List.map (fun (c,_) -> (c, mk_symbol c [] ctxt#type_int Uninterp)) classmap0)@
    (List.map (fun (c,_) -> (c, mk_symbol c [] ctxt#type_int Uninterp)) interfmap0)
  in
  
  let rec string_of_type t =
    match t with
      Bool -> "bool"
    | Void -> "void"
    | IntType -> "int"
    | RealType -> "real"
    | Char -> "char"
    | InductiveType (i, []) -> i
    | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
    | ObjType l -> "class " ^ l
    | StructType sn -> "struct " ^ sn
    | PtrType t -> string_of_type t ^ " *"
    | FuncType ft -> ft
    | PredType ts -> "predicate(" ^ String.concat ", " (List.map string_of_type ts) ^ ")"
    | BoxIdType -> "box"
    | HandleIdType -> "handle"
    | AnyType -> "any"
    | TypeParam x -> x
    | InferredType t -> begin match !t with None -> "?" | Some t -> string_of_type t end
  in
  
  let structmap1 =
    List.map
      (fun (sn, (l, fds_opt)) ->
         let rec iter fmap fds =
           match fds with
             [] -> (sn, (l, Some (List.rev fmap)))
           | Field (lf, gh, t, f,Instance,Public)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else
               iter ((f, (lf, gh, check_pure_type ("", []) [] t))::fmap) fds
         in
         begin
           match fds_opt with
             Some fds -> iter [] fds
           | None -> (sn, (l, None))
         end
      )
      structdeclmap
  in
  
  let structmap = structmap1 @ structmap0 in
  
  let typenode_of_provertype t =
    match t with
      ProverInt -> ctxt#type_int
    | ProverBool -> ctxt#type_bool
    | ProverReal -> ctxt#type_real
    | ProverInductive -> ctxt#type_inductive
  in
  
  let rec provertype_of_type t =
    match t with
      Bool -> ProverBool
    | IntType -> ProverInt
    | RealType -> ProverReal
    | Char -> ProverInt
    | InductiveType _ -> ProverInductive
    | StructType sn -> assert false
    | ObjType n -> ProverInt
    | PtrType t -> ProverInt
    | FuncType _ -> ProverInt
    | PredType t -> ProverInductive
    | BoxIdType -> ProverInt
    | HandleIdType -> ProverInt
    | AnyType -> ProverInductive
    | TypeParam _ -> ProverInductive
    | InferredType t -> begin match !t with None -> t := Some (InductiveType ("unit", [])); ProverInductive | Some t -> provertype_of_type t end
  in
  
  let typenode_of_type t = typenode_of_provertype (provertype_of_type t) in
  
  let isfuncs = if file_type path=Java then [] else
    List.map (fun ftn ->
      let isfuncname = "is_" ^ ftn in
      let domain = [ctxt#type_int] in
      let symb = mk_symbol isfuncname domain ctxt#type_bool Uninterp in
      (isfuncname, (dummy_loc, [], Bool, [PtrType Void], symb))
    ) functypenames
  in
  
  let checksuper (pn,ilist) super sub=(* check wether x is a superclass of y*)
    let rec search a b=
      if a=b then true
      else if b="java.lang.Object" || b="Object" then false
        else 
          let s = match try_assoc' (pn,ilist) b classdeclmap with 
            Some (_,_,_,_,s,_,_,_) -> s 
          | None -> match try_assoc' (pn,ilist) b classmap0 with 
              None -> "Object"
           | Some (_,_,_,_,s,_,_,_) -> s
          in
          search a s
    in
    search super sub
  in
  
  let checkinter (pn,ilist) inter cn=(* check wether y implements the interface x*)
    let s = match try_assoc' (pn,ilist) cn classdeclmap with 
              Some (_,_,_,_,_,s,_,_) -> s
            | None -> match try_assoc' (pn,ilist) cn classmap0 with 
                None -> []
             | Some (_,_,_,_,_,s,_,_) -> s
    in
    let rec iter map=
      match map with
        []-> false
      | n::rest -> match search2' n (pn,ilist) interfdeclmap interfmap0 with
            Some n' when inter=n'-> true
          | _ -> iter rest
    in
    iter s
  in

  let rec compatible_pointees t t0 =
    match (t, t0) with
      (_, Void) -> true
    | (Void, _) -> true
    | (PtrType t, PtrType t0) -> compatible_pointees t t0
    | _ -> t = t0
  in
  
  let rec unfold_inferred_type t =
    match t with
      InferredType t' ->
      begin
        match !t' with
          None -> t
        | Some t -> unfold_inferred_type t
      end
    | _ -> t
  in
  
  let rec unify t1 t2 (pn,ilist)=
    t1 == t2 ||
    match (unfold_inferred_type t1, unfold_inferred_type t2) with
      (InferredType t', InferredType t0') -> if t' = t0' then true else begin t0' := Some t1; true end
    | (t, InferredType t0) -> t0 := Some t; true
    | (InferredType t, t0) -> t := Some t0; true
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
	  let i1 = match search' i1 (pn,ilist) inductivedeclmap with 
	    Some s-> s
	  | None -> i1
	  in
	  let i2 = match search' i2 (pn,ilist) inductivedeclmap with 
	    Some s-> s
	  | None -> i2 
	  in
	  i1=i2 && List.for_all2 (fun a b ->unify a b (pn,ilist)) args1 args2
    | (t1, t2) -> t1 = t2
  in
  
  let rec expect_type_core (pn,ilist) l msg t t0 =
    match (unfold_inferred_type t, unfold_inferred_type t0) with
      (PtrType t, PtrType t0) when compatible_pointees t t0 -> ()
    | (ObjType "null", ObjType _) -> ()
    | (Char, IntType) -> ()
    | (ObjType x, ObjType y) ->
	  let x= match search2' x (pn,ilist) classdeclmap classmap0 with 
	    Some x -> x
	  | None -> match search2' x (pn,ilist) interfdeclmap interfmap0 with 
	      Some x -> x
		| None -> assert(false)
	  in
	  let y= match search2' y (pn,ilist) classdeclmap classmap0 with 
	    Some y -> y
	  | None -> match search2' y (pn,ilist) interfdeclmap interfmap0 with 
	      Some y -> y
		| None -> assert(false)
	  in
      if y="Object"||y="java.lang.Object"||x=y||(checkinter (pn,ilist) y x)||(checksuper (pn,ilist) x y) then ()
	  else static_error l (msg ^ "Type mismatch. Actual: " ^ x ^ ". Expected: " ^ y ^ ".")
    | (PredType ts, PredType ts0) ->
      begin
        match zip ts ts0 with
          None -> static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
        | Some tpairs ->
          List.iter (fun (t, t0) -> expect_type_core (pn,ilist) l msg t t0) tpairs
      end
    | (InductiveType _, AnyType) -> ()
    | _ -> if unify t t0 (pn,ilist) then () else static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
  in
  
  let expect_type (pn,ilist) l t t0 = expect_type_core (pn,ilist) l "" t t0 in
  
  let get_conversion_funcname proverType proverType0 =
    match (proverType, proverType0) with
    | (ProverBool, ProverInductive) -> "boxed_bool"
    | (ProverInt, ProverInductive) -> "boxed_int"
    | (ProverReal, ProverInductive) -> "boxed_real"
    | (ProverInductive, ProverBool) -> "unboxed_bool"
    | (ProverInductive, ProverInt) -> "unboxed_int"
    | (ProverInductive, ProverReal) -> "unboxed_real"
  in
  
  let convert_provertype_expr e proverType proverType0 =
    if proverType = proverType0 then e else CallExpr (expr_loc e, get_conversion_funcname proverType proverType0, [], [], [LitPat e], Static)
  in
  
  let box e t t0 =
    match t0 with TypeParam _ -> convert_provertype_expr e (provertype_of_type t) ProverInductive | _ -> e
  in
  
  let unbox e t0 t =
    match t0 with TypeParam _ -> convert_provertype_expr e ProverInductive (provertype_of_type t) | _ -> e
  in
  
  let (inductivemap1, purefuncmap1, fixpointmap1) =
    let rec iter (pn,ilist) imap pfm fpm ds =
      match ds with
        [] -> (List.rev imap, List.rev pfm, List.rev fpm)
      | Inductive (l, i, tparams, ctors)::ds -> let i=full_name pn i in
        begin
          let rec iter tparams' tparams =
            match tparams with
              [] -> ()
            | x::xs -> if List.mem x tparams' then static_error l "Duplicate type parameter."; iter (x::tparams') xs
          in
          iter [] tparams
        end;
        let rec citer j ctormap pfm ctors =
          match ctors with
            [] -> iter (pn,ilist) ((i, (l, tparams, List.rev ctormap))::imap) pfm fpm ds
          | Ctor (lc, cn, tes)::ctors -> let cn=full_name pn cn in
            if List.mem_assoc cn pfm || List.mem_assoc cn purefuncmap0 then
              static_error lc ("Duplicate pure function name: "^cn)
            else (
              let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
              let csym =
                if ts = [] then
                  alloc_nullary_ctor j cn
                else
                  mk_symbol cn (List.map typenode_of_type ts) ctxt#type_inductive (Proverapi.Ctor (CtorByOrdinal j))
              in
              let purefunc = (cn, (lc, tparams, InductiveType (i, List.map (fun x -> TypeParam x) tparams), ts, csym)) in
              citer (j + 1) ((cn, (lc, ts))::ctormap) (purefunc::pfm) ctors
            )
        in
        citer 0 [] pfm ctors
      | Func (l, Fixpoint, tparams, rto, g1, ps, atomic, functype, contract, body_opt,Static,Public)::ds ->
        let g=full_name pn g1 in
        let _ =
          if List.mem_assoc g pfm || List.mem_assoc g purefuncmap0 then static_error l ("Duplicate pure function name: "^g)
        in
        if not (distinct tparams) then static_error l "Duplicate type parameter names.";
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void."
          | Some rt -> (check_pure_type (pn,ilist) tparams rt)
        in
        if atomic then static_error l "A fixpoint function cannot be atomic.";
        if functype <> None then static_error l "Fixpoint functions cannot implement a function type.";
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
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((p, t)::pmap) ps
          in
          iter [] ps
        in
        let (index, ctorcount, ls, w, wcs) = 
          match body_opt with
            Some ([SwitchStmt (ls, e, cs)], _) -> (
            let ctorcount = List.length cs in
            match e with
              Var (l, x, _) -> (
              match try_assoc_i x pmap with
                None -> static_error l "Fixpoint function must switch on a parameter."
              | Some (index, InductiveType (i, targs)) -> (
                match try_assoc2' (pn,ilist) i imap inductivemap0 with
                  None -> static_error ls "Switch statement cannot precede inductive declaration."
                | Some (l, inductive_tparams, ctormap) ->
                  let (Some tpenv) = zip inductive_tparams targs in
                  let rec iter ctormap wcs cs =
                    match cs with
                      [] ->
                      let _ = 
                        match ctormap with
                          [] -> ()
                        | (cn, _)::_ ->
                          static_error ls ("Missing case: '" ^ cn ^ "'.")
                      in (index, ctorcount, ls, e, wcs)
                    | SwitchStmtClause (lc, cn, xs, body)::cs -> (
                      match try_assoc' (pn,ilist) cn ctormap with
                        None -> static_error lc "No such constructor."
                      | Some (_, ts) ->
                        let xmap =
                          let rec iter xmap ts xs =
                            match (ts, xs) with
                              ([], []) -> xmap
                            | (t::ts, x::xs) ->
                              if List.mem_assoc x pmap then static_error lc "Pattern variable hides parameter.";
                              let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." in
                              iter ((x, instantiate_type tpenv t)::xmap) ts xs
                            | ([], _) -> static_error lc "Too many pattern variables."
                            | _ -> static_error lc "Too few pattern variables."
                          in
                          iter [] ts xs
                        in
                        let tenv = xmap @ pmap in
                        let (lret, body) =
                          match body with
                            [ReturnStmt (lret, Some e)] -> (lret, e)
                          | _ -> static_error lc "Body of switch clause must be a return statement with a result expression."
                        in
                        let rec check_ tenv e =
                          let check e = check_ tenv e in
                          let checkt e = checkt_ tenv e in
                          let promote_numeric e1 e2 ts =
                            let (w1, t1) = check e1 in
                            let (w2, t2) = check e2 in
                            match (t1, t2) with
                              (IntType, RealType) ->
                              let w1 = checkt e1 RealType in
                              ts := Some [RealType; RealType];
                              (w1, w2, RealType)
                            | (t1, t2) ->
                              let w2 = checkt e2 t1 in
                              ts := Some [t1; t1];
                              (w1, w2, t1)
                          in
                          let promote l e1 e2 ts =
                            match promote_numeric e1 e2 ts with
                              (w1, w2, (IntType | RealType)) as result -> result
                            | _ -> static_error l "Expression of type int or real expected."
                          in
                          match e with
                            True l -> (e, boolt)
                          | False l -> (e, boolt)
                          | Null l -> (e, match rt with ObjType id -> ObjType id | TypeParam t -> TypeParam t) (* null is allowed for every object type or a type param*)
                          | Var (l, x, scope) -> (
                            match try_assoc x tenv with
                              None -> (
                                match try_assoc2' (pn,ilist) x pfm purefuncmap0 with
                                  Some (_, tparams, t, [], _) ->
                                  if tparams <> [] then
                                    let targs = List.map (fun _ -> InferredType (ref None)) tparams in
                                    let Some tpenv = zip tparams targs in
                                    scope := Some PureCtor;
                                    (e, instantiate_type tpenv t)
                                  else
                                  begin
                                    scope := Some PureCtor;
                                    (e, t)
                                  end
                                | _ -> static_error l "No such variable or constructor."
                              )
                            | Some t -> scope := Some LocalVar; (e, t)
                            )
                          | Operation (l, ((Eq | Neq) as operator), [e1; e2], ts) ->
                            let (w1, w2, t) = promote_numeric e1 e2 ts in
                            (Operation (l, operator, [w1; w2], ts), boolt)
                          | Operation (l, ((Or | And) as operator), [e1; e2], ts) ->
                            let w1 = checkt e1 boolt in
                            let w2 = checkt e2 boolt in
                            (Operation (l, operator, [w1; w2], ts), boolt)
                          | Operation (l, Not, [e], ts) ->
                            let w = checkt e boolt in
                            (Operation (l, Not, [w], ts), boolt)
                          | Operation (l, ((Le | Lt) as operator), [e1; e2], ts) ->
                            let (w1, w2, t) = promote l e1 e2 ts in
                            (Operation (l, operator, [w1; w2], ts), boolt)
                          | Operation (l, ((Add | Sub) as operator), [e1; e2], ts) ->
                            let (w1, w2, t) = promote l e1 e2 ts in
                            (Operation (l, operator, [w1; w2], ts), t)
                          | Operation (l, ((Mul | Div) as operator), [e1; e2], ts) ->
                            let w1 = checkt e1 RealType in
                            let w2 = checkt e2 RealType in
                            (Operation (l, operator, [w1; w2], ts), RealType)
                          | IntLit (l, n, t) -> t := Some intt; (e, intt)
                          | StringLit (l, s) ->(
						    match file_type path with
						      Java-> (e, ObjType "String")
							| _ -> (e, PtrType Char)
							)
                          | CallExpr (l', g', targes, [], pats, info) -> (
                            match (match try_assoc' (pn,ilist) g' pfm with
                              None -> try_assoc' (pn,ilist) g' purefuncmap0
                            | result -> result)
                            with
                              Some (l, callee_tparams, t0, ts0, _) -> (
                              let (targs, tpenv) =
                                if callee_tparams <> [] && targes = [] then
                                  let targs = List.map (fun _ -> InferredType (ref None)) callee_tparams in
                                  let Some tpenv = zip tparams targs in
                                  (targs, tpenv)
                                else
                                  let targs = List.map (check_pure_type (pn,ilist) tparams) targes in
                                  let tpenv =
                                    match zip callee_tparams targs with
                                      None -> static_error l "Incorrect number of type arguments."
                                    | Some bs -> bs
                                  in
                                  (targs, tpenv)
                              in
                              let t = instantiate_type tpenv t0 in
                              let ts = List.map (instantiate_type tpenv) ts0 in
                              match zip pats ts with
                                None -> static_error l "Incorrect argument count."
                              | Some pts -> (
                                let Some pts = zip pts ts0 in
                                let wpats =
                                List.map (fun ((pat, t), t0) ->
                                  match pat with
                                    LitPat e -> LitPat (box (checkt e t) t t0)
                                  | _ -> static_error l "Patterns are not allowed here."
                                ) pts in
                                (unbox (CallExpr (l, g', targes, [], wpats, info)) t0 t, t)
                                )
                              )
                            | None ->
                              if g' = g1 then
                                match zip pmap pats with
                                  None -> static_error l "Incorrect argument count."
                                | Some pts ->
                                  let (targs, tpenv) =
                                    if tparams <> [] && targes = [] then
                                      let targs = List.map (fun _ -> InferredType (ref None)) tparams in
                                      let Some tpenv = zip tparams targs in
                                      (targs, tpenv)
                                    else
                                      let targs = List.map (check_pure_type (pn,ilist) tparams) targes in
                                      let tpenv =
                                        match zip tparams targs with
                                          None -> static_error l "Incorrect number of type arguments."
                                        | Some bs -> bs
                                      in
                                      (targs, tpenv)
                                  in
                                  let wpats =
                                    List.map (fun ((p, t0), pat) ->
                                      let t = instantiate_type tpenv t0 in
                                      match pat with
                                        LitPat e -> LitPat (box (checkt e t) t t0)
                                      | _ -> static_error l "Patterns are not allowed here."
                                    ) pts
                                  in
                                  let _ =
                                    match flatmap (function ((p, t), LitPat e) -> if p = x then [e] else []) pts with
                                      [Var (l, x, _)] when List.mem_assoc x xmap -> ()
                                    | _ -> static_error l "Inductive argument of recursive call must be switch clause pattern variable."
                                  in
                                  let rt' = instantiate_type tpenv rt in
                                  (unbox (CallExpr (l, g', targes, [], wpats, info)) rt rt', rt')
                              else
                                static_error l ("No such pure function: " ^ g')
                            )
                          | IfExpr (l, e1, e2, e3) ->
                            let w1 = checkt e1 boolt in
                            let (w2, t) = check e2 in
                            let w3  = checkt e3 t in
                            (IfExpr (l, w1, w2, w3), t)
                          | SwitchExpr (l, e, cs, tref) ->
                            let (w, t) = check e in
                            begin
                              match t with
                                InductiveType (i, targs) ->
                                begin
                                  let (_, tparams, ctormap) = assoc2 i imap inductivemap0 in
                                  let (Some tpenv) = zip tparams targs in
                                  let rec iter t0 wcs ctors cs =
                                    match cs with
                                      [] ->
                                      if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors));
                                      begin
                                        match t0 with
                                          None -> static_error l "Switch expressions with zero cases are not yet supported."
                                        | Some t0 -> tref := Some (targs, t0); (SwitchExpr (l, w, List.rev wcs, tref), t0)
                                      end
                                    | SwitchExprClause (lc, cn, xs, e)::cs ->
                                      begin
                                        match try_assoc' (pn,ilist) cn ctormap with
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
                                                iter2 ts xs ((x, instantiate_type tpenv t)::xenv)
                                            in
                                            iter2 ts xs []
                                          in
                                          let (w, t) = check_ (xenv@tenv) e in
                                          let t0 =
                                            match t0 with
                                              None -> Some t
                                            | Some t0 -> expect_type (pn,ilist) (expr_loc e) t t0; Some t0
                                          in
                                          let ctors = List.filter (fun (ctorname, _) -> ctorname <> cn) ctors in
                                          iter t0 (SwitchExprClause (lc, cn, xs, w)::wcs) ctors cs
                                      end
                                  in
                                  iter None [] ctormap cs
                                end
                            end
                          | e -> static_error (expr_loc e) "Expression form not allowed in fixpoint function body."
                        and checkt_ tenv e t0 =
                          match (e, t0) with
                            (IntLit (l, n, t), PtrType _) when eq_big_int n zero_big_int -> t:=Some IntType; e
                          | (IntLit (l, n, t), RealType) -> t:=Some RealType; e
                          | _ ->
                            let (w, t) = check_ tenv e in
                            expect_type (pn,ilist) (expr_loc e) t t0;
                            w
                        in
                        let wbody = checkt_ tenv body rt in
						let Some cn= search' cn (pn,ilist) ctormap in
                        iter (List.remove_assoc cn ctormap) (SwitchStmtClause (lc, cn, xs, [ReturnStmt (lret, Some wbody)])::wcs) cs
                      )
                  in
                  iter ctormap [] cs
                )
              | _ -> static_error l "Switch operand is not an inductive value."
              )
            )
          | _ -> static_error l "Body of fixpoint function must be switch statement."
        in
        let fsym = mk_symbol g (List.map (fun (p, t) -> typenode_of_type t) pmap) (typenode_of_type rt) (Proverapi.Fixpoint index) in
        iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, rt, pmap, ls, w, wcs,pn,ilist))::fpm) ds
      | _::ds -> iter (pn,ilist) imap pfm fpm ds
    in
    let rec iter' (imap,pfm,fpm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) imap pfm fpm ds) rest
      | [] -> (imap,pfm,fpm)
    in
    iter' ([],isfuncs,[]) ps
  in
  
  let inductivemap = inductivemap1 @ inductivemap0 in
  let fixpointmap = fixpointmap1 @ fixpointmap0 in
  
  let () =
    let inhabited_map = List.map (fun (i, info) -> (i, (info, ref 0))) inductivemap1 in
    let rec check_inhabited i l ctors status =
      if !status = 2 then
        ()
      else
      begin
        status := 1;
        let rec find_ctor ctors =
          match ctors with
            [] -> static_error l "Inductive datatype is not inhabited."
          | (_, (_, pts))::ctors ->
            let rec check_paramtypes pts =
              match pts with
                [] -> ()
              | pt::pts ->
                begin
                  match pt with
                    InductiveType (i0, _) ->
                    begin
                      if List.mem_assoc i0 inductivemap0 then
                        check_paramtypes pts
                      else
                        let ((l0, _, ctors0), status0) = List.assoc i0 inhabited_map in
                        if !status0 = 1 then
                          find_ctor ctors
                        else
                        begin
                          check_inhabited i0 l0 ctors0 status0;
                          check_paramtypes pts
                        end
                    end
                  | _ -> check_paramtypes pts
                end
            in
            check_paramtypes pts
        in
        find_ctor ctors;
        status := 2
      end
    in
    List.iter (fun (i, ((l, _, ctors), status)) -> check_inhabited i l ctors status) inhabited_map
  in
  
  let get_unique_var_symb x t = ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) [] in
  
  let mk_predfam p l arity ts inputParamCount = (p, (l, arity, ts, get_unique_var_symb p (PredType ts), inputParamCount)) in
  
  let malloc_block_pred_map1 = 
    match file_type path with
    Java-> (flatmap (function (cn, (_)) -> [(cn, mk_predfam ("malloc_block_" ^ cn) dummy_loc 0 [ObjType cn] (Some 1))] | _ -> []) classdeclmap) @
           (flatmap (function (i, (_)) -> [(i, mk_predfam ("malloc_block_" ^ i) dummy_loc 0 [ObjType i] (Some 1))] | _ -> []) interfdeclmap) @
           (flatmap (function (cn, (_)) -> [(cn, mk_predfam ("malloc_block_" ^ cn) dummy_loc 0 [ObjType cn] (Some 1))] | _ -> []) classmap0) @
           (flatmap (function (i, (_)) -> [(i, mk_predfam ("malloc_block_" ^ i) dummy_loc 0 [ObjType i] (Some 1))] | _ -> []) interfmap0)
    | _ -> flatmap (function (sn, (l, Some _)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) l 0 
            [PtrType (StructType sn)] (Some 1))] | _ -> []) structmap1 
  in
  
  let malloc_block_pred_map = malloc_block_pred_map1 @ malloc_block_pred_map0 in

  let field_pred_map1 = (* dient om dingen te controleren bij read/write controle v velden*)
    match file_type path with
    Java-> flatmap
      (fun (cn, (_,_, fds_opt,_,_,_,_,_)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (l, t,_)) ->
              ((cn, fn), mk_predfam (cn ^ "_" ^ fn) l 0 [ObjType cn; t] (Some 1))
             )
             fds
      )
      classfmap
    | _ ->
    flatmap
      (fun (sn, (_, fds_opt)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (l, gh, t)) ->
              ((sn, fn), mk_predfam (sn ^ "_" ^ fn) l 0 [PtrType (StructType sn); t] (Some 1))
             )
             fds
      )
      structmap1
  in
  
  let field_pred_map = field_pred_map1 @ field_pred_map0 in
  
  let structpreds1 = List.map (fun (_, p) -> p) malloc_block_pred_map1 @ List.map (fun (_, p) -> p) field_pred_map1 in
  
  let predfammap1 =
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyDecl (l, p, arity, tes, inputParamCount)::ds -> let p=full_name pn p in
        let ts = List.map (check_pure_type (pn,ilist) []) tes in
        begin
          match try_assoc2' (pn,ilist) p pm predfammap0 with
            Some (l0, arity0, ts0, symb0, inputParamCount0) ->
            if arity <> arity0 || ts <> ts0 || inputParamCount <> inputParamCount0 then static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.");
            iter (pn,ilist) pm ds
          | None ->
            iter (pn,ilist) (mk_predfam p l arity ts inputParamCount::pm) ds
        end
      | _::ds -> iter (pn,ilist) pm ds
      | [] -> List.rev pm
    in
    let rec iter' pm ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter (pn,il) pm ds) rest
      | [] -> pm
    in
    iter' [] ps
  in
  
  let (boxmap, predfammap1) =
    let rec iter (pn,ilist) bm pfm ds =
      match ds with
        [] -> (bm, pfm)
      | BoxClassDecl (l, bcn, ps, inv, ads, hpds)::ds -> let bcn= full_name pn bcn in
        if List.mem_assoc bcn pfm || List.mem_assoc bcn purefuncmap0 then static_error l "Box class name clashes with existing predicate name.";
        let default_hpn = bcn ^ "_handle" in
        if List.mem_assoc default_hpn pfm then static_error l ("Default handle predicate name '" ^ default_hpn ^ "' clashes with existing predicate name.");
        let boxpmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              if List.mem_assoc x pmap then static_error l "Duplicate parameter name.";
              if startswith x "old_" then static_error l "Box parameter name cannot start with old_.";
              iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
          in
          iter [] ps
        in
        let old_boxpmap = List.map (fun (x, t) -> ("old_" ^ x, t)) boxpmap in
        let pfm = mk_predfam bcn l 0 (BoxIdType::List.map (fun (x, t) -> t) boxpmap) (Some 1)::pfm in
        let pfm = mk_predfam default_hpn l 0 (HandleIdType::BoxIdType::[]) (Some 1)::pfm in
        let amap =
          let rec iter amap ads =
            match ads with
              [] -> List.rev amap
            | ActionDecl (l, an, ps, pre, post)::ads ->
              if List.mem_assoc an amap then static_error l "Duplicate action name.";
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Action parameter clashes with box parameter.";
                    if List.mem_assoc x pmap then static_error l "Duplicate action parameter name.";
                    if startswith x "old_" then static_error l "Action parameter name cannot start with old_.";
                    iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
                in
                iter [] ps
              in
              iter ((an, (l, pmap, pre, post))::amap) ads
          in
          iter [] ads
        in
        let (pfm, hpm) =
          let rec iter pfm hpm hpds =
            match hpds with
              [] -> (pfm, List.rev hpm)
            | HandlePredDecl (l, hpn, ps, inv, pbcs)::hpds ->
              if List.mem_assoc hpn hpm then static_error l "Duplicate handle predicate name.";
              if List.mem_assoc hpn pfm then static_error l "Handle predicate name clashes with existing predicate name.";
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Handle predicate parameter clashes with box parameter.";
                    if List.mem_assoc x pmap then static_error l "Duplicate handle predicate parameter name.";
                    if startswith x "old_" then static_error l "Handle predicate parameter name cannot start with old_.";
                    iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
                in
                iter [] ps
              in
              iter (mk_predfam hpn l 0 (HandleIdType::BoxIdType::List.map (fun (x, t) -> t) pmap) (Some 1)::pfm) ((hpn, (l, pmap, inv, pbcs))::hpm) hpds
          in
          iter pfm [] hpds
        in
        iter (pn,ilist) ((bcn, (l, boxpmap, inv, amap, hpm,pn,ilist))::bm) pfm ds
      | _::ds -> iter (pn,ilist) bm pfm ds
    in
    let rec iter' (bm,pfm) ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter (pn,il) bm pfm ds) rest
      | [] -> (bm,pfm)
    in
    iter' ([],predfammap1) ps
  in
  
  let predfammap = predfammap1 @ structpreds1 @ predfammap0 in (* TODO: Check for name clashes here. *)
  let (predctormap1, purefuncmap1) =
    let rec iter (pn,ilist) pcm pfm ds =
      match ds with
        PredCtorDecl (l, p, ps1, ps2, body)::ds -> let p=full_name pn p in
        begin
          match try_assoc2' (pn,ilist) p pfm purefuncmap0 with
            Some _ -> static_error l "Predicate constructor name clashes with existing pure function name."
          | None -> ()
        end;
        begin
          match try_assoc' (pn,ilist) p predfammap with
            Some _ -> static_error l "Predicate constructor name clashes with existing predicate or predicate familiy name."
          | None -> ()
        end;
        let ps1 =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              begin
                match try_assoc x pmap with
                  Some _ -> static_error l "Duplicate parameter name."
                | _ -> ()
              end;
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::pmap) ps
          in
          iter [] ps1
        in
        let ps2 =
          let rec iter psmap pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              begin
                match try_assoc x psmap with
                  Some _ -> static_error l "Duplicate parameter name."
                | _ -> ()
              end;
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::psmap) ((x, t)::pmap) ps
          in
          iter ps1 [] ps2
        in
        let funcsym = mk_symbol p (List.map (fun (x, t) -> typenode_of_type t) ps1) ctxt#type_inductive Proverapi.Uninterp in
        let pf = (p, (l, [], PredType (List.map (fun (x, t) -> t) ps2), List.map (fun (x, t) -> t) ps1, funcsym)) in
        iter (pn,ilist) ((p, (l, ps1, ps2, body, funcsym,pn,ilist))::pcm) (pf::pfm) ds
      | [] -> (pcm, pfm)
      | _::ds -> iter (pn,ilist) pcm pfm ds
    in
    let rec iter' (pcm,pfm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) pcm pfm ds) rest
      | [] -> (pcm,pfm)
    in
    iter' ([],purefuncmap1) ps
  in
  let purefuncmap = purefuncmap1 @ purefuncmap0 in
  let predctormap = predctormap1 @ predctormap0 in
  
  let funcnames = if file_type path=Java then [] else
  let ds= (match ps with[PackageDecl(_,"",[],ds)] ->ds) in
  list_remove_dups (flatmap (function (Func (l, (Regular|Lemma), tparams, rt, g, ps, atomic, ft, c, b,Static,Public)) -> [g] | _ -> []) ds) 
  in
  
  let check_classnamelist (pn,ilist) is =
    List.map (fun (l, i) -> match search2' i (pn,ilist) classdeclmap classmap0 with 
      None -> static_error l "No such class name."
    | Some s-> s) is
  in
  
  let check_funcnamelist is =
    List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such regular function name."; i) is 
  in
  
  let predinstmap1 =
    flatmap
      begin
        function
          (sn, (_, Some fmap)) ->
          flatmap
            begin
              function
                (f, (l, Real, t)) ->
                begin
                let predinst p =
                  ((sn ^ "_" ^ f, []),
                   (l, [sn, PtrType (StructType sn); "value", t], Some 1,
                    (let fref = new fieldref f in
                    fref#set_parent sn;
                    fref#set_range t;
                    CallPred (l, p, [], [LitPat (AddressOf (l, Read (l, Var (l, sn, ref (Some LocalVar)), fref))); LitPat (Var (l, "value", ref (Some LocalVar)))]))
                    ,"",[]
                   )
                  )
                in
                match t with
                  PtrType _ ->
                  let pref = new predref "pointer" in
                  pref#set_domain [PtrType (PtrType Void); PtrType Void];
                  [predinst pref]
                | IntType ->
                  let pref = new predref "integer" in
                  pref#set_domain [PtrType IntType; IntType];
                  [predinst pref]
                | _ -> []
                end
              | _ -> []
            end
            fmap
        | _ -> []
      end
      structmap1
  in
  
  let predinstmap1 = 
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyInstanceDecl (l, p, is, xs, body)::ds ->
        let (arity, ps, inputParamCount) =
          match try_assoc' (pn,ilist) p predfammap with
            None -> static_error l ("No such predicate family: "^p)
          | Some (_, arity, ps, _, inputParamCount) -> (arity, ps, inputParamCount)
        in
        if List.length is <> arity then static_error l "Incorrect number of indexes.";
        let pxs =
          match zip ps xs with
            None -> static_error l "Incorrect number of parameters."
          | Some pxs -> pxs
        in
        let fns = match file_type path with
          Java-> check_classnamelist (pn,ilist) is
        | _ -> check_funcnamelist is 
        in
        let pfns = (full_name pn p, fns) in
        let _ = if List.mem_assoc pfns pm || List.mem_assoc pfns predinstmap0 then static_error l "Duplicate predicate family instance." in
        let rec iter2 xm pxs =
          match pxs with
            [] -> iter (pn,ilist) ((pfns, (l, List.rev xm, inputParamCount, body,pn,ilist))::pm) ds
          | (t0, (te, x))::xs -> 
            let t = check_pure_type (pn,ilist) [] te in
            let _ =
            expect_type (pn,ilist) l t t0
            in
            if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
            iter2 ((x, t)::xm) xs
        in
        iter2 [] pxs
      | _::ds -> iter (pn,ilist) pm ds
      | [] -> List.rev pm
    in
    let rec iter' pm ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) pm ds) rest
      | [] -> pm
    in
    iter' predinstmap1 ps
  in
  
  let predinstmap = predinstmap1 @ predinstmap0 in
  
  let rec check_expr (pn,ilist) tparams tenv e =
    let check e = check_expr (pn,ilist) tparams tenv e in
    let checkt e t0 = check_expr_t (pn,ilist) tparams tenv e t0 in
    let promote_numeric e1 e2 ts =
      let (w1, t1) = check e1 in
      let (w2, t2) = check e2 in
      match (t1, t2) with
        (IntType, RealType) ->
        let w1 = checkt e1 RealType in
        ts := Some [RealType; RealType];
        (w1, w2, RealType)
      | (t1, t2) ->
        let w2 = checkt e2 t1 in
        ts := Some [t1; t1];
        (w1, w2, t1)
    in
    let promote l e1 e2 ts =
      match promote_numeric e1 e2 ts with
        (w1, w2, (IntType | RealType | PtrType _)) as result -> result
      | _ -> static_error l "Expression of type int, real, or pointer type expected."
    in
    match e with
      True l -> (e, boolt)
    | False l -> (e, boolt)
    | Null l -> (e, ObjType "null")
    | Var (l, x, scope) ->
      begin
      match try_assoc x tenv with
        None ->
        begin
          match try_assoc' (pn,ilist) x purefuncmap with
            Some (_, tparams, t, [], _) ->
            if tparams <> [] then
            begin
              let targs = List.map (fun _ -> InferredType (ref None)) tparams in
              let Some tpenv = zip tparams targs in
              scope := Some PureCtor;
              (e, instantiate_type tpenv t)
            end
            else
            begin
              scope := Some PureCtor; (e, t)
            end
          | _ ->
            begin
              if List.mem x funcnames then
                match file_type path with
                Java -> static_error l "In java methods can't be used as pointers"
                | _ -> scope := Some FuncName; (e, PtrType Void)
              else
                begin
                  match try_assoc' (pn,ilist) x predfammap with
                    Some (_, arity, ts, _, _) ->
                    if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
                    scope := Some PredFamName;
                    (e, PredType ts)
                  | None ->
                    static_error l ("No such variable, constructor, regular function, or predicate: "^x)
                end
            end
        end
      | Some t -> scope := Some LocalVar; (e, t)
      end
    | PredNameExpr (l, g) ->
      begin
        match try_assoc' (pn,ilist) g predfammap with
          Some (_, arity, ts, _, _) ->
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
          (e, PredType ts)
        | None -> static_error l "No such predicate."
      end
    | Operation (l, (Eq | Neq as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote_numeric e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt)
    | Operation (l, (Or | And as operator), [e1; e2], ts) -> 
      let w1 = checkt e1 boolt in
      let w2 = checkt e2 boolt in
      (Operation (l, operator, [w1; w2], ts), boolt)
    | Operation (l, Not, [e], ts) -> 
      let w = checkt e boolt in
      (Operation (l, Not, [w], ts), boolt)
    | Operation (l, (Le | Lt as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote l e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt)
    | Operation (l, (Add | Sub as operator), [e1; e2], ts) ->
      let (w1, t1) = check e1 in
	  let (w2, t2) = check e2 in
      begin
        match t1 with
          PtrType _ ->
          let w2 = checkt e2 intt in
          ts:=Some [t1; IntType];
          (Operation (l, operator, [w1; w2], ts), t1)
        | IntType | RealType ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (Operation (l, operator, [w1; w2], ts), t)
		| ObjType "String" as t->
		  let w2 = checkt e2 t in
		  ts:=Some [t1; ObjType "String"];
		  (Operation (l, operator, [w1; w2], ts), t1)
        | _ -> static_error l ("Operand of addition or subtraction must be pointer, integer, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2))
      end
    | Operation (l, (Mul | Div as operator), [e1; e2], ts) ->
      let w1 = checkt e1 RealType in
      let w2 = checkt e2 RealType in
      (Operation (l, operator, [w1; w2], ts), RealType)
    | IntLit (l, n, t) -> t := Some intt; (e, intt)
    | ClassLit (l, s) -> (e, ObjType "Class")
    | StringLit (l, s) -> (match file_type path with
	    Java-> (e, ObjType "String")
	  | _ -> (e, PtrType Char))
    | CastExpr (l, te, e) -> 
      let t = check_pure_type (pn,ilist) tparams te in
      let w =
        match (e, t) with
          (IntLit (_, n, tp), PtrType _) -> tp := Some t; e
        | _ -> match file_type path with
            Java -> e
          | _ -> checkt e t
      in
      (CastExpr (l, te, w), t)
    | Read (l, e, f) -> let (w, t) = check_deref false true (pn,ilist) l tparams tenv e f in (Read (l, w, f), t)
    | Deref (l, e, tr) ->
      let (w, t) = check e in
      begin
        match t with
          PtrType t0 -> tr := Some t0; (Deref (l, w, tr), t0)
        | _ -> static_error l "Operand must be pointer."
      end
    | AddressOf (l, e) ->
      let (w, t) = check e in
      (AddressOf (l, w), PtrType t)
    | CallExpr (l, g', targes, [], pats, info) -> (
      match try_assoc' (pn,ilist) g' purefuncmap with
        Some (_, callee_tparams, t0, ts, _) -> (
        let (targs, tpenv) =
          if callee_tparams <> [] && targes = [] then
            let targs = List.map (fun _ -> InferredType (ref None)) callee_tparams in
            let Some tpenv = zip callee_tparams targs in
            (targs, tpenv)
          else
            let targs = List.map (check_pure_type (pn,ilist) tparams) targes in
            let tpenv =
              match zip callee_tparams targs with
                None -> static_error l "Incorrect number of type arguments."
              | Some bs -> bs
            in
            (targs, tpenv)
        in
        match zip pats ts with
          None -> static_error l "Incorrect argument count."
        | Some pts -> (
          let wpats =
          List.map (fun (pat, t0) ->
            match pat with
              LitPat e ->
              let t = instantiate_type tpenv t0 in
              LitPat (box (checkt e t) t t0)
            | _ -> static_error l "Patterns are not allowed here."
          ) pts
          in
          let t = instantiate_type tpenv t0 in
          (unbox (CallExpr (l, g', targes, [], wpats, info)) t0 t, t)
          )
        )
      | None -> if g'="getClass" && (file_type path)=Java then
                  match pats with
                   [LitPat target] -> let w = checkt target (ObjType "Object") in (CallExpr (l, g', [], [], [LitPat w], info), ObjType "Class")
                else static_error l ("No such pure function: "^g')
      )
    | IfExpr (l, e1, e2, e3) ->
      let w1 = checkt e1 boolt in
      let (w2, t) = check e2 in
      let w3 = checkt e3 t in
      (IfExpr (l, w1, w2, w3), t)
    | FuncNameExpr _ -> (e, PtrType Void)
    | SwitchExpr (l, e, cs, tref) ->
      let (w, t) = check e in
      begin
        match t with
          InductiveType (i, targs) ->
          begin
            let (_, tparams, ctormap) = List.assoc i inductivemap in
            let (Some tpenv) = zip tparams targs in
            let rec iter t0 wcs ctors cs =
              match cs with
                [] ->
                if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors));
                begin
                  match t0 with
                    None -> static_error l "Switch expressions with zero clauses are not yet supported."
                  | Some t0 -> tref := Some (targs, t0); (SwitchExpr (l, w, wcs, tref), t0)
                end
              | SwitchExprClause (lc, cn, xs, e)::cs ->
                begin
                  match try_assoc' (pn,ilist) cn ctormap with
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
                          iter2 ts xs ((x, instantiate_type tpenv t)::xenv)
                      in
                      iter2 ts xs []
                    in
                    let (w, t) = check_expr (pn,ilist) tparams (xenv@tenv) e in
                    let t0 =
                      match t0 with
                        None -> Some t
                      | Some t0 -> expect_type (pn,ilist) (expr_loc e) t t0; Some t0
                    in
                    let ctors = List.filter (fun (ctorname, _) -> ctorname <> cn) ctors in
                    iter t0 (SwitchExprClause (lc, cn, xs, w)::wcs) ctors cs
                end
            in
            iter None [] ctormap cs
          end
        | _ -> static_error l "Switch expression operand must be inductive value."
      end
    | e -> static_error (expr_loc e) "Expression form not allowed here."
  and check_expr_t (pn,ilist) tparams tenv e t0 =
    match (e, t0) with
      (IntLit (l, n, t), PtrType _) when eq_big_int n zero_big_int -> t:=Some IntType; e
    | (IntLit (l, n, t), RealType) -> t:=Some RealType; e
    | (IntLit (l, n, t), Char) ->
      if not (le_big_int zero_big_int n && le_big_int n (big_int_of_int 127)) then
        static_error l "Integer literal used as char must be between 0 and 127.";
      t:=Some IntType; e
    | _ ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in expect_type (pn,ilist) (expr_loc e) t t0; w
  and check_deref is_write pure (pn,ilist) l tparams tenv e f =
    let check_ok gh =
      if is_write && pure && gh = Real then static_error l "Cannot write in a pure context."
    in
    let (w, t) = check_expr (pn,ilist) tparams tenv e in
    begin
    match t with
    | PtrType (StructType sn) ->
      begin
      match List.assoc sn structmap with
        (_, Some fds) ->
        begin
          match try_assoc' (pn,ilist) f#name fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.")
          | Some (_, gh, t) -> check_ok gh; f#set_parent sn; f#set_range t; (w, t)
        end
      | (_, None) -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' was declared without a body.")
      end
    | ObjType sn ->
      begin
      match try_assoc' (pn,ilist) sn classfmap with
        Some (_,_, Some fds,_,_,_,_,_) ->
        begin
          match try_assoc' (pn,ilist) f#name fds with
            None -> static_error l ("No such field in class '" ^ sn ^ "'.")
          | Some (_, t,_) -> check_ok Real; f#set_parent sn; f#set_range t; (w, t)
        end
      | Some (_,_,None,_,_,_,_,_) -> static_error l ("Invalid dereference; class '" ^ sn ^ "' was declared without a body.")
      end
    | _ -> static_error l "Target expression of field dereference should be of type pointer-to-struct."
    end
  in

  let check_pat (pn,ilist) l tparams tenv t p =
    match p with
      LitPat e -> let w = check_expr_t (pn,ilist) tparams tenv e t in (LitPat w, tenv)
    | VarPat x ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
      (p, (x, t)::tenv)
    | DummyPat -> (p, tenv)
  in
  
  let rec check_pats (pn,ilist) l tparams tenv ts ps =
    match (ts, ps) with
      ([], []) -> ([], tenv)
    | (t::ts, p::ps) ->
      let (wpat, tenv) = check_pat (pn,ilist) l tparams tenv t p in
      let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv ts ps in
      (wpat::wpats, tenv)
    | ([], _) -> static_error l "Too many patterns"
    | (_, []) -> static_error l "Too few patterns"
  in

  let rec check_pred (pn,ilist) tparams tenv p =
    match p with
      Access (l, e, f, v) ->
      let (w, t) = check_deref false true (pn,ilist) l tparams tenv e f in
      let (wv, tenv') = check_pat (pn,ilist) l tparams tenv t v in
      (Access (l, w, f, wv), tenv')
    | CallPred (l, p, ps0, ps) ->
      let (arity, xs, inputParamCount) =
        match try_assoc' (pn,ilist) p#name predfammap with
          Some (_, arity, xs, _, inputParamCount) -> (arity, xs, inputParamCount)
        | None ->
          begin
            match try_assoc' (pn,ilist) p#name tenv with
              None -> static_error l ("No such predicate: "^p#name)
            | Some (PredType ts) -> (0, ts, None)
            | Some _ -> static_error l ("Variable is not of predicate type: "^p#name)
          end
      in
      begin
        if List.length ps0 <> arity then static_error l "Incorrect number of indexes.";
        let ts0 = match file_type path with
          Java-> list_make arity (ObjType "Class")
        | _   -> list_make arity (PtrType Void)
        in
        let (wps0, tenv) = check_pats (pn,ilist) l tparams tenv ts0 ps0 in
        let (wps, tenv) = check_pats (pn,ilist) l tparams tenv xs ps in
        p#set_domain (ts0 @ xs); p#set_inputParamCount inputParamCount; (CallPred (l, p, wps0, wps), tenv)
      end
    | ExprPred (l, e) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in (ExprPred (l, w), tenv)
    | Sep (l, p1, p2) ->
      let (p1, tenv) = check_pred (pn,ilist) tparams tenv p1 in
      let (p2, tenv) = check_pred (pn,ilist) tparams tenv p2 in
      (Sep (l, p1, p2), tenv)
    | IfPred (l, e, p1, p2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let (wp1, _) = check_pred (pn,ilist) tparams tenv p1 in
      let (wp2, _) = check_pred (pn,ilist) tparams tenv p2 in
      (IfPred (l, w, wp1, wp2), tenv)
    | SwitchPred (l, e, cs) ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      begin
      match t with
      | InductiveType (i, targs) ->
        begin
        match try_assoc' (pn,ilist) i inductivemap with
          None -> static_error l "Switch operand is not an inductive value."
        | Some (_, inductive_tparams, ctormap) ->
          let (Some tpenv) = zip inductive_tparams targs in
          let rec iter wcs ctormap cs =
            match cs with
              [] ->
              let _ = 
                match ctormap with
                  [] -> ()
                | (cn, _)::_ ->
                  static_error l ("Missing case: '" ^ cn ^ "'.")
              in (SwitchPred (l, w, wcs), tenv)
            | SwitchPredClause (lc, cn, xs, ref_xsInfo, body)::cs ->
              begin
              match try_assoc' (pn,ilist) cn ctormap with
                None -> static_error lc "No such constructor."
              | Some (_, ts) ->
                let (xmap, xsInfo) =
                  let rec iter xmap xsInfo ts xs =
                    match (ts, xs) with
                      ([], []) -> (xmap, List.rev xsInfo)
                    | (t::ts, x::xs) ->
                      if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
                      let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." in
                      let xInfo = match t with TypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None in
                      iter ((x, instantiate_type tpenv t)::xmap) (xInfo::xsInfo) ts xs
                    | ([], _) -> static_error lc "Too many pattern variables."
                    | _ -> static_error lc "Too few pattern variables."
                  in
                  iter [] [] ts xs
                in
                ref_xsInfo := Some xsInfo;
                let tenv = xmap @ tenv in
                let (wbody, _) = check_pred (pn,ilist)  tparams tenv body in
				let Some cn= search' cn (pn,ilist) ctormap in
                iter (SwitchPredClause (lc, cn, xs, ref_xsInfo, wbody)::wcs) (List.remove_assoc cn ctormap) cs
              end
          in
          iter [] ctormap cs
        end
      | _ -> static_error l "Switch operand is not an inductive value."
      end
    | EmpPred l -> (p, tenv)
    | CoefPred (l, coef, body) ->
      let (wcoef, tenv) = check_pat (pn,ilist) l tparams tenv RealType coef in
      let (wbody, tenv) = check_pred (pn,ilist) tparams tenv body in
      (CoefPred (l, wcoef, wbody), tenv)
  in
  
  let boxmap =
    List.map
      begin
        fun (bcn, (l, boxpmap, inv, amap, hpmap,pn,ilist)) ->
        let (winv, boxvarmap) = check_pred (pn,ilist) [] boxpmap inv in
        let old_boxvarmap = List.map (fun (x, t) -> ("old_" ^ x, t)) boxvarmap in
        let amap =
        List.map
          (fun (an, (l, pmap, pre, post)) ->
             let pre = check_expr_t (pn,ilist) [] ([("actionHandle", HandleIdType)] @ pmap @ boxvarmap) pre boolt in
             let post = check_expr_t (pn,ilist) [] ([("actionHandle", HandleIdType)] @ pmap @ boxvarmap @ old_boxvarmap) post boolt in
             (an, (l, pmap, pre, post))
          )
          amap
        in
        let hpmap =
        List.map
          (fun (hpn, (l, pmap, inv, pbcs)) ->
             let inv = check_expr_t (pn,ilist) [] ([("predicateHandle", HandleIdType)] @ pmap @ boxvarmap) inv boolt in
             (hpn, (l, pmap, inv, pbcs))
          )
          hpmap
        in
        (bcn, (l, boxpmap, winv, boxvarmap, amap, hpmap))
      end
      boxmap
  in
  
  let rec vars_used e =
    match e with
      True l -> []
    | False l -> []
    | Null l -> []
    | Var (l, x, scope) -> begin match !scope with Some LocalVar -> [x] | Some _ -> [] end
    | Operation (l, op, es, _) ->
      flatmap vars_used es
    | IntLit (l, _, _) -> []
    | StringLit (_, _) -> []
    | ClassLit (l, _) -> []
    | Read (l, e, f) -> vars_used e
    | Deref (l, e, t) -> vars_used e
    | AddressOf (l, e) -> vars_used e
    | CallExpr (l, g, targs, [], pats, _) ->
      flatmap (fun (LitPat e) -> vars_used e) pats
    | IfExpr (l, e, e1, e2) -> vars_used e @ vars_used e1 @ vars_used e2
    | SwitchExpr (l, e, cs, _) ->
      vars_used e @
      flatmap
        (fun (SwitchExprClause (l, c, xs, e)) ->
         let xs' = vars_used e in
         List.filter (fun x -> not (List.mem x xs)) xs'
        )
        cs
    | PredNameExpr (l, _) -> []
    | FuncNameExpr _ -> []
    | CastExpr (_, _, e) -> vars_used e
    | SizeofExpr (_, _) -> []
  in
  
  let assert_expr_fixed fixed e =
    let used = vars_used e in
    let nonfixed = List.filter (fun x -> not (List.mem x fixed)) used in
    if nonfixed <> [] then
      let xs = String.concat ", " (List.map (fun x -> "'" ^ x ^ "'") nonfixed) in
      static_error (expr_loc e) ("Preciseness check failure: non-fixed variable(s) " ^ xs ^ " used in input expression.")
  in
  
  let fixed_pat_fixed_vars pat =
    match pat with
      LitPat (Var (_, x, scope)) when !scope = Some LocalVar -> [x]
    | LitPat _ -> []
    | VarPat x -> [x]
    | DummyPat -> []
  in
  
  let assume_pat_fixed fixed pat =
    fixed_pat_fixed_vars pat @ fixed
  in
  
  let assert_pats_fixed l fixed pats =
    List.iter (function (LitPat e) -> assert_expr_fixed fixed e | _ -> static_error l "Non-fixed pattern used in input position.") pats
  in
  
  let assume_pats_fixed fixed pats =
    flatmap fixed_pat_fixed_vars pats @ fixed
  in
  
  let expr_is_fixed fixed e =
    let used = vars_used e in
    List.for_all (fun x -> List.mem x fixed) used
  in
  
  let rec check_pred_precise fixed p =
    match p with
      Access (l, et, f, pv) ->
      assert_expr_fixed fixed et;
      assume_pat_fixed fixed pv
    | CallPred (l, g, pats0, pats) ->
      begin
        match g#inputParamCount with
          None -> static_error l "Preciseness check failure: callee is not precise."
        | Some n ->
          let (inpats, outpats) = take_drop n pats in
          let inpats = pats0 @ inpats in
          assert_pats_fixed l fixed inpats;
          assume_pats_fixed fixed outpats
      end
    | ExprPred (l, Operation (_, Eq, [Var (_, x, scope); e2], _)) when !scope = Some LocalVar ->
      if not (List.mem x fixed) && expr_is_fixed fixed e2 then
        x::fixed
      else
        fixed
    | ExprPred (_, _) -> fixed
    | Sep (l, p1, p2) ->
      let fixed = check_pred_precise fixed p1 in
      check_pred_precise fixed p2
    | IfPred (l, e, p1, p2) ->
      assert_expr_fixed fixed e;
      let fixed1 = check_pred_precise fixed p1 in
      let fixed2 = check_pred_precise fixed p2 in
      intersect fixed1 fixed2
    | SwitchPred (l, e, cs) ->
      assert_expr_fixed fixed e;
      let rec iter fixed' cs =
        match cs with
          [] -> fixed'
        | SwitchPredClause (l, c, xs, _, p)::cs ->
          let fixed = check_pred_precise (xs@fixed) p in
          iter (intersect fixed' fixed) cs
      in
      iter fixed cs
    | EmpPred l -> fixed
    | CoefPred (l, coefpat, p) ->
      begin
        match coefpat with
          LitPat e -> assert_expr_fixed fixed e
        | VarPat x -> static_error l "Precision check failure: variable patterns not supported as coefficients."
        | DummyPat -> ()
      end;
      check_pred_precise fixed p
  in
  
  let predinstmap =
    List.map
      (
        fun
          (pfns, (l, xs, inputParamCount, body,pn,ilist)) ->
          let (wbody, _) = check_pred (pn,ilist) [] xs body in
          begin
            match inputParamCount with
              None -> ()
            | Some n ->
              let (inps, outps) = take_drop n (List.map (fun (x, t) -> x) xs) in
              let fixed = check_pred_precise inps wbody in
              List.iter
                (fun x ->
                 if not (List.mem x fixed) then
                   static_error l ("Preciseness check failure: body does not fix output parameter '" ^ x ^ "'."))
                outps
          end;
          (pfns, (l, xs, inputParamCount, wbody))
      )
      predinstmap
  in
  
  let predctormap =
    List.map
      (
        function
          (g, (l, ps1, ps2, body, funcsym,pn,ilist)) ->
          let (wbody, _) = check_pred (pn,ilist) [] (ps1 @ ps2) body in
          (g, (l, ps1, ps2, wbody, funcsym))
      )
      predctormap
  in

  let check_ghost ghostenv l e =
    let rec iter e =
      match e with
        Var (l, x, _) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context."
      | Operation (l, _, es, _) -> List.iter iter es
      | CallExpr (l, _, targs, [], pats,_) -> List.iter (function LitPat e -> iter e | _ -> ()) pats
      | IfExpr (l, e1, e2, e3) -> (iter e1; iter e2; iter e3)
      | _ -> ()
    in
    iter e
  in

  let funcnameterms = List.map (fun fn -> (fn, get_unique_var_symb fn (PtrType Void))) funcnames
  in
  
  let sizeof l t =
    match t with
      Void | Char -> 1
    | IntType -> 4
    | PtrType _ -> 4
    | _ -> static_error l ("Taking the size of type " ^ string_of_type t ^ " is not yet supported.")
  in
  
  let field_offsets =
    flatmap
      begin
        function
          (sn, (_, Some fmap)) ->
          let offsets = flatmap (fun (f, (_, gh, _)) -> if gh = Ghost then [] else [((sn, f), get_unique_var_symb (sn ^ "_" ^ f ^ "_offset") IntType)]) fmap in
          begin
            match offsets with
              ((_, _), offset0)::_ ->
              ignore (ctxt#assume (ctxt#mk_eq offset0 (ctxt#mk_intlit 0)))
            | _ -> ()
          end;
          offsets
        | _ -> []
      end
      structmap
  in
  
  let field_offset f = (List.assoc (f#parent, f#name) field_offsets) in
  let field_address t f = ctxt#mk_add t (field_offset f) in
  
  let pure_func_symb g (pn,ilist)= let Some(_, _, _, _, symb) = try_assoc' (pn,ilist) g purefuncmap in symb in
  
  let convert_provertype term proverType proverType0 (pn,ilist)= (* TODO: Cache these pure function symbols as soon as there is support for a Java prelude. *)
    if proverType = proverType0 then term else ctxt#mk_app (pure_func_symb (get_conversion_funcname proverType proverType0) (pn,ilist)) [term]
  in
  
  let prover_convert_term term t t0 (pn,ilist)=
    if t = t0 then term else convert_provertype term (provertype_of_type t) (provertype_of_type t0) (pn,ilist)
  in

  let rec eval_core (pn,ilist) assert_term read_field (env: (string * 'termnode) list) e : 'termnode =
    let ev = eval_core (pn,ilist) assert_term read_field env in
    let check_overflow l min t max =
      begin
      match assert_term with
        Some assert_term when not disable_overflow_check ->
        assert_term l (ctxt#mk_le min t) "Potential arithmetic underflow.";
        assert_term l (ctxt#mk_le t max) "Potential arithmetic overflow."
      | _ -> ()
      end;
      t
    in
    match e with
      True l -> ctxt#mk_true
    | False l -> ctxt#mk_false
    | Null l -> ctxt#mk_intlit 0
    | Var (l, x, scope) ->
      begin
        if !scope = None then print_endline (string_of_loc l);
        let (Some scope) = !scope in
        match scope with
          LocalVar -> (try(List.assoc x env)with Not_found -> static_error l ("Local var wasn't found: "^x))
        | PureCtor -> let Some (lg, tparams, t, [], s) = try_assoc' (pn,ilist) x purefuncmap in ctxt#mk_app s []
        | FuncName -> (List.assoc x funcnameterms)
        | PredFamName -> let Some (_, _, _, symb, _) = (try_assoc' (pn,ilist) x predfammap)in symb
      end
    | PredNameExpr (l, g) -> let Some (_, _, _, symb, _) = (try_assoc' (pn,ilist) g predfammap) in symb
    | CastExpr (l, te, e) ->
      let t = check_pure_type (pn,ilist) [] te in
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
      else ctxt#mk_reallit_of_num (Num.num_of_big_int n)
    | ClassLit (l,s) -> 
      let Some symb= search' s (pn,ilist) class_symbols in
      ctxt#mk_app (List.assoc symb class_symbols) []
    | StringLit (l, s) -> (match file_type path with
	    Java -> get_unique_var_symb "stringLiteral" (ObjType "String")
	  | _ -> get_unique_var_symb "stringLiteral" (PtrType Char))
    | CallExpr (l, g, targs, [], pats,_) ->
      if g="getClass" && (file_type path=Java) then 
        match pats with
          [LitPat target] ->
          ctxt#mk_app get_class_symbol [ev target]
      else
      begin
        match try_assoc' (pn,ilist) g purefuncmap with
          None -> static_error l ("No such pure function: "^g)
        | Some (lg, tparams, t, pts, s) -> ctxt#mk_app s (List.map (function (LitPat e) -> ev e) pats)
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
        | Some [PtrType t; IntType] ->
          let n = sizeof l t in
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_add (ev e1) (ctxt#mk_mul (ctxt#mk_intlit n) (ev e2))) max_ptr_term
        | Some [RealType; RealType] ->
          ctxt#mk_real_add (ev e1) (ev e2)
        | _ -> static_error l "Internal error in eval."
      end
    | Operation (l, Sub, [e1; e2], ts) ->
      begin
        match !ts with
          Some [IntType; IntType] ->
          check_overflow l min_int_term (ctxt#mk_sub (ev e1) (ev e2)) max_int_term
        | Some [PtrType t; IntType] ->
          let n = sizeof l t in
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_sub (ev e1) (ctxt#mk_mul (ctxt#mk_intlit n) (ev e2))) max_ptr_term
        | Some [RealType; RealType] ->
          ctxt#mk_real_sub (ev e1) (ev e2)
      end
    | Operation (l, Mul, [e1; e2], ts) -> ctxt#mk_real_mul (ev e1) (ev e2)
    | Operation (l, Div, [e1; e2], ts) ->
      let rec eval_reallit e =
        match e with
          IntLit (l, n, t) -> Num.num_of_big_int n
        | _ -> static_error (expr_loc e) "The denominator of a division must be a literal."
      in
      ctxt#mk_real_mul (ev e1) (ctxt#mk_reallit_of_num (Num.div_num (Num.num_of_int 1) (eval_reallit e2)))
    | Operation (l, Le, [e1; e2], ts) -> (match !ts with Some ([IntType; IntType] | [PtrType _; PtrType _]) -> ctxt#mk_le (ev e1) (ev e2) | Some [RealType; RealType] -> ctxt#mk_real_le (ev e1) (ev e2))
    | Operation (l, Lt, [e1; e2], ts) -> (match !ts with Some ([IntType; IntType] | [PtrType _; PtrType _]) -> ctxt#mk_lt (ev e1) (ev e2) | Some [RealType; RealType] -> ctxt#mk_real_lt (ev e1) (ev e2))
    | Read(l, e, f) ->
      begin
        match read_field with
          None -> static_error l "Cannot use field dereference in this context."
        | Some (read_field, deref_pointer) -> read_field l (ev e) f
      end
    | Deref (l, e, t) ->
      begin
        match read_field with
          None -> static_error l "Cannot use field dereference in this context."
        | Some (read_field, deref_pointer) ->
          let (Some t) = !t in
          deref_pointer l (ev e) t
      end
    | AddressOf (l, e) ->
      begin
        match e with
          Read (le, e, f) -> 
          (* MS Visual C++ behavior: http://msdn.microsoft.com/en-us/library/hx1b6kkd.aspx (= depends on command-line switches and pragmas) *)
          (* GCC documentation is not clear about it. *)
          field_address (ev e) f
        | _ -> static_error l "Taking the address of this expression is not supported."
      end
    | FuncNameExpr fn -> (List.assoc fn funcnameterms)
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
      let (Some (targs, tp)) = !tref in
      let symbol = ctxt#mk_symbol g (ctxt#get_type t :: List.map (fun (x, t) -> ctxt#get_type t) env) (typenode_of_type tp) (Proverapi.Fixpoint 0) in
      let fpclauses =
        List.map
          (function (SwitchExprClause (_, cn, ps, e)) ->
             let Some (_, tparams, _, pts, csym) = try_assoc' (pn,ilist) cn purefuncmap in
             let apply gvs cvs =
               let Some genv = zip ("#value"::List.map (fun (x, t) -> x) env) gvs in
               let Some penv = zip ps cvs in
               let penv =
                 if tparams = [] then penv else
                 let Some penv = zip penv pts in
                 let Some tpenv = zip tparams targs in
                 List.map
                   (fun ((pat, term), typ) ->
                    match typ with
                      TypeParam x -> (pat, convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv)) (pn,ilist))
                    | _ -> (pat, term)
                   )
                   penv
               in
               let env = penv@genv in
               eval_core (pn,ilist) None None env e
             in
             (csym, apply)
          )
          cs
      in
      ctxt#set_fpclauses symbol 0 fpclauses;
      ctxt#mk_app symbol (t::List.map (fun (x, t) -> t) env)
    | _ -> static_error (expr_loc e) "Construct not supported in this position."
  in
  
  let eval (pn,ilist) = eval_core (pn,ilist) None in

  let _ =
    List.iter
    (function
       (g, (l, t, pmap, _, Var (_, x, _), cs,pn,ilist)) ->
       let rec index_of_param i x0 ps =
         match ps with
           [] -> assert false
         | (x, tp)::ps -> if x = x0 then (i, tp) else index_of_param (i + 1) x0 ps
       in
       let (i, InductiveType (_, targs)) = index_of_param 0 x pmap in
       let Some(_,_,_,_,fsym) =try_assoc' (pn,ilist) g purefuncmap in
       let clauses =
         List.map
           (function (SwitchStmtClause (lc, cn, pats, [ReturnStmt (_, Some e)])) ->
              let (_, tparams, _, ts, ctorsym) = match try_assoc' (pn,ilist) cn purefuncmap with Some x -> x in
              let eval_body gts cts =
                let Some pts = zip pmap gts in
                let penv = List.map (fun ((p, tp), t) -> (p, t)) pts in
                let Some patenv = zip pats cts in
                let patenv =
                  if tparams = [] then patenv else
                  let Some tpenv = zip tparams targs in
                  let Some patenv = zip patenv ts in
                  List.map
                    (fun ((x, term), typ) ->
                     let term =
                     match typ with
                       TypeParam x -> convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv))(pn,ilist)
                     | _ -> term
                     in
                     (x, term)
                    )
                    patenv
                in
                eval (pn,ilist) None (patenv @ penv) e
              in
              (ctorsym, eval_body)
           )
           cs
       in
       ctxt#set_fpclauses fsym i clauses
    )
    fixpointmap1
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
         let h' = List.map (fun ((g, literal), coef, ts, size) -> ((ctxt#pprint g, literal), ctxt#pprint coef, List.map (fun t -> ctxt#pprint t) ts, size)) h in
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
  
  let assert_expr (pn,ilist) env e h env l msg = assert_term (eval (pn,ilist) None env e) h env l msg in
  
  let success() = () in
  
  let branch cont1 cont2 =
    stats#branch;
    in_temporary_context (fun _ -> cont1());
    in_temporary_context (fun _ -> cont2())
  in
  
  let evalpat (pn,ilist) ghostenv env pat tp cont =
    if pat == real_unit_pat then cont ghostenv env real_unit else
    match pat with
      LitPat e -> cont ghostenv env (eval (pn,ilist) None env e)
    | VarPat x -> let t = get_unique_var_symb x tp in cont (x::ghostenv) (update env x t) t
    | DummyPat -> let t = get_unique_var_symb "dummy" tp in cont ghostenv env t
  in
  
  let rec evalpats (pn,ilist) ghostenv env pats tps cont =
    match (pats, tps) with
      ([], []) -> cont ghostenv env []
    | (pat::pats, tp::tps) -> evalpat (pn,ilist) ghostenv env pat tp (fun ghostenv env t -> evalpats (pn,ilist) ghostenv env pats tps (fun ghostenv env ts -> cont ghostenv env (t::ts)))
  in

  let real_mul l t1 t2 =
    if t1 == real_unit then t2 else if t2 == real_unit then t1 else ctxt#mk_real_mul t1 t2
  in
  
  let real_div l t1 t2 =
    if t2 == real_unit then t1 else static_error l "Real division not yet supported."
  in
  
  let assume_field h0 f tp tv tcoef cont =
    let (_, (_, _, _, symb, _)) =(List.assoc (f#parent, f#name) field_pred_map)in
    let rec iter h =
      match h with
        [] -> cont (((symb, true), tcoef, [tp; tv], None)::h0)
      | ((g, true), tcoef', [tp'; _], _)::h when g == symb && tcoef' == real_unit -> assume_neq tp tp' (fun _ -> iter h)
      | _::h -> iter h
    in
    iter h0
  in
  
  let rec assume_pred (pn,ilist) h ghostenv (env: (string * 'termnode) list) p coef size_first size_all cont =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ -> with_context (Executing (h, env, pred_loc p, "Producing assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval (pn,ilist) None env in
    match p with
    | Access (l, e, f, rhs) ->
      let te = ev e in evalpat (pn,ilist) ghostenv env rhs f#range (fun ghostenv env t -> assume_field h f te t coef (fun h -> cont h ghostenv env))
    | CallPred (l, g, pats0, pats) ->
      let g_symb =
        match try_assoc' (pn,ilist) g#name predfammap with
          Some (_, _, _, symb, _) -> (symb, true)
        | None -> (List.assoc g#name env, false)
      in
      evalpats (pn,ilist) ghostenv env (pats0 @ pats) g#domain (fun ghostenv env ts -> cont ((g_symb, coef, ts, size_first)::h) ghostenv env)
    | ExprPred (l, e) -> assume (ev e) (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) -> assume_pred (pn,ilist) h ghostenv env p1 coef size_first size_all (fun h ghostenv env -> assume_pred (pn,ilist) h ghostenv env p2 coef size_all size_all cont)
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ = cont h ghostenv env in
      branch (fun _ -> assume (ev e) (fun _ -> assume_pred (pn,ilist) h ghostenv env p1 coef size_all size_all cont)) (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> assume_pred (pn,ilist) h ghostenv env p2 coef size_all size_all cont))
    | SwitchPred (l, e, cs) ->
      let cont h _ _ = cont h ghostenv env in
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, patsInfo, p)::cs ->
          branch
            (fun _ ->
               let Some (_, tparams, _, tps, cs) = try_assoc' (pn,ilist) cn purefuncmap in
               let Some pts = zip pats tps in
               let xts =
                 if tparams = [] then
                   List.map (fun (x, tp) -> let term = get_unique_var_symb x tp in (x, term, term)) pts
                 else
                   let Some patsInfo = !patsInfo in
                   let Some pts = zip pts patsInfo in
                   List.map
                     (fun ((x, tp), info) ->
                      match info with
                        None -> let term = get_unique_var_symb x tp in (x, term, term)
                      | Some proverType ->
                        let term = ctxt#mk_app (mk_symbol x [] (typenode_of_provertype proverType) Uninterp) [] in
                        let term' = convert_provertype term proverType ProverInductive (pn,ilist) in
                        (x, term', term)
                     )
                     pts
               in
               let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
               assume_eq t (ctxt#mk_app cs (List.map (fun (x, t, _) -> t) xts)) (fun _ -> assume_pred (pn,ilist) h (pats @ ghostenv) (xenv @ env) p coef size_all size_all cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env
    | CoefPred (l, coef', body) ->
      evalpat (pn,ilist) ghostenv env coef' RealType (fun ghostenv env coef' -> assume_pred (pn,ilist) h ghostenv env body (real_mul l coef coef') size_first size_all cont)
    )
  in
  
  let definitely_equal t1 t2 =
    let result = t1 == t2 || (ctxt#query (ctxt#mk_eq t1 t2)) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  in
  
  let predname_eq g1 g2 =
    match (g1, g2) with
      ((g1, literal1), (g2, literal2)) -> if literal1 && literal2 then g1 == g2 else definitely_equal g1 g2
  in
  
  let match_chunk (pn,ilist) ghostenv env l g coef coefpat pats (g', coef0, ts0, size0) =
    let match_pat ghostenv env pat t cont =
      match (pat, t) with
        (LitPat e, t) -> if definitely_equal (eval (pn,ilist) None env e) t then cont ghostenv env else None
      | (VarPat x, t) -> cont (x::ghostenv) (update env x t)
      | (DummyPat, t) -> cont ghostenv env
    in
    let rec iter ghostenv env pats ts =
      match (pats, ts) with
        (pat::pats, t::ts) -> match_pat ghostenv env pat t (fun ghostenv env -> iter ghostenv env pats ts)
      | ([], []) -> Some (coef0, ts0, size0, ghostenv, env)
    in
      if predname_eq g g' then
        begin
          if coef == real_unit && coefpat == real_unit_pat && coef0 == real_unit then iter ghostenv env pats ts0 else
          match coefpat with
            LitPat e -> if definitely_equal (real_mul l coef (eval (pn,ilist) None env e)) coef0 then iter ghostenv env pats ts0 else None
          | VarPat x -> iter (x::ghostenv) (update env x (real_div l coef0 coef)) pats ts0
          | DummyPat -> iter ghostenv env pats ts0
        end
      else
        None
  in
  
  let lookup_points_to_chunk h0 env l f_symb t =
    let rec iter h =
      match h with
        [] -> assert_false h0 env l ("No matching heap chunk: " ^ ctxt#pprint f_symb)
      | ((g, true), coef, [t0; v], _)::_ when g == f_symb && definitely_equal t0 t -> v
      | _::h -> iter h
    in
    iter h0
  in

  let read_field h env l t f =
    let (_, (_, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
    lookup_points_to_chunk h env l f_symb t
  in
  
  let (pointer_pred_symb, int_pred_symb) =
    match file_type path with
      Java -> (real_unit, real_unit) (* Anything, doesn't matter. *)
    | _ ->
      let (_, _, _, pointer_pred_symb, _) = List.assoc "pointer" predfammap in
      let (_, _, _, int_pred_symb, _) = List.assoc "integer" predfammap in
      (pointer_pred_symb, int_pred_symb)
  in
  
  let pointee_pred_symb l pointeeType =
    match pointeeType with
      PtrType _ -> pointer_pred_symb
    | IntType -> int_pred_symb
    | _ -> static_error l "Dereferencing pointers of this type is not yet supported."
  in
  
  let deref_pointer h env l pointerTerm pointeeType =
    lookup_points_to_chunk h env l (pointee_pred_symb l pointeeType) pointerTerm
  in

  let assert_chunk (pn,ilist) h ghostenv env l g coef coefpat pats cont =
    let rec iter hprefix h =
      match h with
        [] -> []
      | chunk::h ->
        let matches =
          match match_chunk (pn,ilist) ghostenv env l g coef coefpat pats chunk with
            None -> []
          | Some (coef, ts, size, ghostenv, env) -> [(hprefix @ h, coef, ts, size, ghostenv, env)]
        in
          matches @ iter (chunk::hprefix) h
    in
    match iter [] h with
      [] -> assert_false h env l ("No matching heap chunks: " ^ (match g with (g, _) -> ctxt#pprint g))
(*      
    | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
    | _ -> assert_false h env l "Multiple matching heap chunks."
*)
    | (h, coef, ts, size, ghostenv, env)::_ -> cont h coef ts size ghostenv env
  in
  
  let rec assert_pred (pn,ilist) h ghostenv env p coef (cont: 'termnode heap -> string list -> 'termnode env -> int option -> unit) =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ -> with_context (Executing (h, env, pred_loc p, "Consuming assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval (pn,ilist) None env in
    let access l coefpat e f rhs =
      let (_, (_, _, _, symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
      assert_chunk (pn,ilist) h ghostenv env l (symb, true) coef coefpat [LitPat e; rhs] (fun h coef ts size ghostenv env -> cont h ghostenv env size)
    in
    let callpred l coefpat g pats0 pats =
      let g_symb =
        match try_assoc' (pn,ilist) g#name predfammap with
          Some (_, _, _, symb, _) -> (symb, true)
        | None -> (List.assoc (g#name) env, false)
      in
      assert_chunk (pn,ilist) h ghostenv env l g_symb coef coefpat (pats0 @ pats) (fun h coef ts size ghostenv env -> cont h ghostenv env size)
    in
    match p with
    | Access (l, e, f, rhs) -> access l real_unit_pat e f rhs
    | CallPred (l, g, pats0, pats) -> callpred l real_unit_pat g pats0 pats
    | ExprPred (l, e) ->
      assert_expr (pn,ilist) env e h env l "Cannot prove condition."; cont h ghostenv env None
    | Sep (l, p1, p2) ->
      assert_pred (pn,ilist) h ghostenv env p1 coef (fun h ghostenv env size -> assert_pred (pn,ilist) h ghostenv env p2 coef (fun h ghostenv env _ -> cont h ghostenv env size))
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ _ = cont h ghostenv env None in
      branch
        (fun _ ->
           assume (ev e) (fun _ ->
             assert_pred (pn,ilist) h ghostenv env p1 coef cont))
        (fun _ ->
           assume (ctxt#mk_not (ev e)) (fun _ ->
             assert_pred (pn,ilist) h ghostenv env p2 coef cont))
    | SwitchPred (l, e, cs) ->
      let cont h _ _ _ = cont h ghostenv env None in
      let t = ev e in
      let rec iter cs =
        match cs with
          SwitchPredClause (lc, cn, pats, patsInfo, p)::cs ->
          let Some (_, tparams, _, tps, ctorsym) = try_assoc' (pn,ilist) cn purefuncmap in
          let Some pts = zip pats tps in
          let (xs, xenv) =
            if tparams = [] then
              let xts = List.map (fun (x, tp) -> (x, get_unique_var_symb x tp)) pts in
              let xs = List.map (fun (x, t) -> t) xts in
              (xs, xts)
            else
              let Some patsInfo = !patsInfo in
              let Some pts = zip pts patsInfo in
              let xts =
                List.map
                  (fun ((x, tp), info) ->
                   match info with
                     None -> let term = get_unique_var_symb x tp in (x, term, term)
                   | Some proverType ->
                     let term = ctxt#mk_app (mk_symbol x [] (typenode_of_provertype proverType) Uninterp) [] in
                     let term' = convert_provertype term proverType ProverInductive (pn,ilist)in
                     (x, term', term)
                  )
                  pts
              in
              let xs = List.map (fun (x, t, _) -> t) xts in
              let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
              (xs, xenv)
          in
          branch
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym xs) (fun _ -> assert_pred (pn,ilist) h (pats @ ghostenv) (xenv @ env) p coef cont))
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
      PureStmt (l, s) -> assigned_variables s
    | NonpureStmt (l, _, s) -> assigned_variables s
    | Assign (l, x, e) -> [x]
    | DeclStmt (l, t, x, e) -> []
    | Write (l, e, f, e') -> []
    | WriteDeref (l, e, e') -> []
    | CallStmt (l, g, targs, es, _) -> []
    | IfStmt (l, e, ss1, ss2) -> block_assigned_variables ss1 @ block_assigned_variables ss2
    | SwitchStmt (l, e, cs) -> flatmap (fun (SwitchStmtClause (_, _, _, ss)) -> block_assigned_variables ss) cs
    | Assert (l, p) -> []
    | Leak (l, p) -> []
    | Open (l, g, ps0, ps1, coef) -> []
    | Close (l, g, ps0, ps1, coef) -> []
    | ReturnStmt (l, e) -> []
    | WhileStmt (l, e, p, ss, _) -> block_assigned_variables ss
    | BlockStmt (l, ss) -> block_assigned_variables ss
    | PerformActionStmt (lcb, nonpure_ctxt, bcn, pre_boxargs, lch, pre_handlepredname, pre_handlepredargs, lpa, actionname, actionargs, atomic, body, closeBraceLoc, post_boxargs, lph, post_handlepredname, post_handlepredargs) ->
      block_assigned_variables body
    | SplitFractionStmt (l, p, pats, coefopt) -> []
    | MergeFractionsStmt (l, p, pats) -> []
    | CreateBoxStmt (l, x, bcn, es, handleClauses) -> []
    | CreateHandleStmt (l, x, hpn, e) -> []
    | DisposeBoxStmt (l, bcn, pats, handleClauses) -> []
    | GotoStmt _ -> []
    | LabelStmt _ -> []
    | InvariantStmt _ -> []
  in

  let get_points_to (pn,ilist) h p predSymb l cont =
    assert_chunk (pn,ilist) h [] [("x", p)] l (predSymb, true) real_unit DummyPat [LitPat (Var (dummy_loc, "x", ref (Some LocalVar))); VarPat "y"] (fun h coef ts size ghostenv env ->
      cont h coef (lookup env "y"))
  in
    
  let get_field (pn,ilist) h t f l cont =
    let (_, (_, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
    get_points_to (pn,ilist) h t f_symb l cont
  in
  
  let functypemap1 =
    let rec iter functypemap ds =
      match ds with
        [] -> List.rev functypemap
      | FuncTypeDecl (l, gh, rt, ftn, xs, (pre, post))::ds ->
        let (pn,ilist) = ("",[]) in
        let _ = if List.mem_assoc ftn functypemap || List.mem_assoc ftn functypemap0 then static_error l "Duplicate function type name." in
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        let (pre, post) =
          let (wpre, tenv) = check_pred (pn,ilist) [] (xmap @ [("this", PtrType Void)]) pre in
          let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
          let (wpost, tenv) = check_pred (pn,ilist) [] postmap post in
          (wpre, wpost)
        in
        iter ((ftn, (l, gh, rt, xmap, pre, post))::functypemap) ds
      | _::ds -> iter functypemap ds
    in
    if file_type path=Java then [] else
    (match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    )
  in
  
  let functypemap = functypemap1 @ functypemap0 in
  
  let check_func_header_compat (pn,ilist) l msg (k, tparams, rt, xmap, atomic, pre, post) (k0, tparams0, rt0, xmap0, atomic0, cenv0, pre0, post0) =
    if k <> k0 then static_error l (msg ^ "Not the same kind of function.");
    let tpenv =
      match zip tparams tparams0 with
        None -> static_error l (msg ^ "Type parameter counts do not match.")
      | Some bs -> List.map (fun (x, x0) -> (x, TypeParam x0)) bs
    in
    begin
      match (rt, rt0) with
        (None, None) -> ()
      | (Some rt, Some rt0) -> expect_type_core (pn,ilist) l (msg ^ "Return types: ") (instantiate_type tpenv rt) rt0
      | _ -> static_error l (msg ^ "Return types do not match.")
    end;
    begin
      match zip xmap xmap0 with
        None -> static_error l (msg ^ "Parameter counts do not match.")
      | Some pairs ->
        List.iter
          (fun ((x, t), (x0, t0)) ->
           expect_type_core (pn,ilist) l (msg ^ "Parameter '" ^ x ^ "': ") t0 (instantiate_type tpenv t);
          )
          pairs
    end;
    if atomic <> atomic0 then static_error l (msg ^ "Atomic clauses do not match.");
    push();
    let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
    let env0 = List.map (fun (x, e) -> (x, eval (pn,ilist) None env0_0 e)) cenv0 in
    assume_pred (pn,ilist) [] [] env0 pre0 real_unit None None (fun h _ env0 ->
      let (Some bs) = zip xmap env0_0 in
      let env = List.map (fun ((p, _), (p0, v)) -> (p, v)) bs in
      assert_pred (pn,ilist) h [] env pre real_unit (fun h _ env _ ->
        let (result, env) =
          match rt with
            None -> (None, env)
          | Some t -> let result = get_unique_var_symb "result" t in (Some result, ("result", result)::env)
        in
        assume_pred (pn,ilist) h [] env post real_unit None None (fun h _ _ ->
          let env0 =
            match result with
              None -> env0
            | Some v -> ("result", v)::env0
          in
          assert_pred (pn,ilist) h [] env0 post0 real_unit (fun h _ env0 _ ->
            with_context (Executing (h, env0, l, "Leak check.")) (fun _ -> if h <> [] then assert_false h env0 l (msg ^ "Implementation leaks heap chunks."))
          )
        )
      )
    );
    pop()
  in
  
  let assume_is_functype fn ftn =
    let (_, _, _, _, symb) = List.assoc ("is_" ^ ftn) purefuncmap in
    ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true))
  in
  
  let (funcmap1, prototypes_implemented) =
    let rec iter pn ilist funcmap prototypes_implemented ds =
      match ds with
        [] -> (funcmap, List.rev prototypes_implemented)
      | Func (l, k, tparams, rt, fn, xs, atomic, functype_opt, contract_opt, body,Static,Public)::ds when k <> Fixpoint -> let fn= full_name pn fn in
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) tparams rt) in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        let (pre, pre_tenv, post) =
          match contract_opt with
            None -> static_error l "Non-fixpoint function must have contract."
          | Some (pre, post) ->
            let (wpre, pre_tenv) = check_pred (pn,ilist) tparams xmap pre in
            let postmap = match rt with None -> pre_tenv | Some rt -> ("result", rt)::pre_tenv in
            let (wpost, tenv) = check_pred (pn,ilist) tparams postmap post in
            (wpre, pre_tenv, wpost)
        in
        if atomic && body <> None then static_error l "Implementing atomic functions is not yet supported.";
        begin
          match functype_opt with
            None -> ()
          | Some ftn ->
            if body = None then static_error l "A function prototype cannot implement a function type.";
            begin
              match try_assoc ftn functypemap with
                None -> static_error l "No such function type."
              | Some (_, gh, rt0, xmap0, pre0, post0) ->
                let cenv0 = List.map (fun (x, t) -> (x, Var (l, x, ref (Some LocalVar)))) xmap0 @ [("this", FuncNameExpr fn)] in
                let k' = match gh with Real -> Regular | Ghost -> Lemma in
                check_func_header_compat (pn,ilist) l "Function type implementation check: " (k, tparams, rt, xmap, atomic, pre, post) (k', [], rt0, xmap0, false, cenv0, pre0, post0);
                if gh = Real then
                  assume_is_functype fn ftn
            end
        end;
        begin
          let body' = match body with None -> None | Some body -> Some (Some body) in
          match try_assoc2 fn funcmap funcmap0 with
            None -> iter pn ilist ((fn, (l, k, tparams, rt, xmap, atomic, pre, pre_tenv, post, body',Static,Public))::funcmap) prototypes_implemented ds
          | Some (l0, k0, tparams0, rt0, xmap0, atomic0, pre0, pre_tenv0, post0, Some _,Static,Public) ->
            if body = None then
              static_error l "Function prototype must precede function implementation."
            else
              static_error l "Duplicate function implementation."
          | Some (l0, k0, tparams0, rt0, xmap0, atomic0, pre0, pre_tenv0, post0, None,Static,Public) ->
            if body = None then static_error l "Duplicate function prototype.";
            let cenv0 = List.map (fun (x, t) -> (x, Var (dummy_loc, x, ref (Some LocalVar)))) xmap0 in
            check_func_header_compat (pn,ilist) l "Function prototype implementation check: " (k, tparams, rt, xmap, atomic, pre, post) (k0, tparams0, rt0, xmap0, atomic0, cenv0, pre0, post0);
            iter pn ilist ((fn, (l, k, tparams, rt, xmap, atomic, pre, pre_tenv, post, body',Static,Public))::funcmap) ((fn, l0)::prototypes_implemented) ds
        end
      | _::ds -> iter pn ilist funcmap prototypes_implemented ds
    in
    let rec iter' (funcmap,prototypes_implemented) ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter pn il funcmap prototypes_implemented ds) rest
      | [] -> (funcmap,prototypes_implemented)
    in
    iter' ([],[]) ps
  in
  
  let funcmap = funcmap1 @ funcmap0 in
  
  let interfmap1 = if file_type path<>Java then [] else
    List.map
      (fun (ifn, (l,specs,pn,ilist)) ->
         let rec iter mmap meth_specs =
           match meth_specs with
             [] -> (ifn, (l,(List.rev mmap),pn,ilist))
           | MethSpec (lm, t, n, ps, co,fb,v)::meths ->
             if List.mem_assoc n mmap then
               static_error lm "Duplicate method name."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
                 | ManifestTypeExpr (_, Bool) -> Bool
                 | IdentTypeExpr(lt, sn) ->
                     match search2' sn (pn,ilist) interfdeclmap interfmap0 with
                       Some i -> ObjType i
                     | None -> match search2' sn (pn,ilist) classdeclmap classmap0 with
                         Some cn -> ObjType cn
                       | None ->static_error lt ("No such class or interface: "^sn)
                 | _ -> static_error (type_expr_loc te) "Invalid return type of this method."
               in
               let check_t t=
                 match t with
                   Some ManifestTypeExpr (_, Void) -> None
                 | Some t-> Some (check_type t)
                 | None -> None
               in
               let xmap =
                 let rec iter xm xs =
                   match xs with
                    [] -> List.rev xm
                  | (te, x)::xs -> if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
                      let t = check_pure_type (pn,ilist) [] te in
                      iter ((x, t)::xm) xs
                 in
                 iter [] ps
               in
               let (pre, post) =
                 match co with
                   None -> static_error lm ("Non-fixpoint function must have contract: "^n)
                 | Some (pre, post) ->
                   let (pre, tenv) = check_pred (pn,ilist) [] xmap pre in
                   let postmap = match check_t t with None -> tenv | Some rt -> ("result", rt)::tenv in
                   let (post, _) = check_pred (pn,ilist) [] postmap post in
                   (pre, post)
               in
               iter ((n, (lm,check_t t, xmap, pre, post,fb,v))::mmap) meths
             )
         in
          begin
           iter [] specs
         end
      )
      interfdeclmap
  in
  
  let interfmap=
    let rec iter map0 map1=
      match map0 with
        [] -> map1
      | (i, (l0,meths0,pn0,ilist0)) as elem::rest->
        match try_assoc i map1 with
          None -> iter rest (elem::map1)
        | Some (l1,meths1,pn1,ilist1) ->
          let match_meths meths0 meths1=
            let rec iter meths0 meths1=
              match meths0 with
                [] -> meths1
              | (mn, (lm0,rt0,xmap0,pre0,post0,fb0,v0)) as elem::rest ->
                match try_assoc mn meths1 with
                  None-> iter rest (elem::meths1)
                | Some(lm1,rt1,xmap1,pre1,post1,fb1,v1) -> 
                  let cenv0 = List.map (fun (x, t) -> (x, Var (lm0, x, ref (Some LocalVar)))) xmap0 in
                  check_func_header_compat (pn1,ilist1) lm1 "Method specification check: " (Regular,[],rt1, xmap1,false, pre1, post1) (Regular, [], rt0, xmap0, false, cenv0, pre0, post0);
                  iter rest meths1
            in
            iter meths0 meths1
          in
          let meths'= match_meths meths0 meths1 in
          iter rest ((i,(l1,meths',pn1,ilist1))::map1)
    in
    iter interfmap0 interfmap1
  in
  
  let classmethmap = if file_type path<>Java then [] else
    List.map
      (fun (cn, (l,meths_opt, fds,constr,super,interfs,pn,ilist)) ->
         let rec iter mmap meths =
           match meths with
             [] -> (cn, (l,Some (List.rev mmap),fds,constr,super,interfs,pn,ilist))
           | Meth (lm, t, n, ps, co, ss,fb,v)::meths ->
             let xmap =
                 let rec iter xm xs =
                   match xs with
                    [] -> List.rev xm
                  | (te, x)::xs -> if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
                      let t = check_pure_type (pn,ilist) [] te in
                      iter ((x, t)::xm) xs
                 in
                 iter [] ps
             in
             let rec equal_types x c=
                 match x with
                 [] -> List.length c==0
                |(name,t)::xrest -> match c with
                  []-> false
                  | (name',t')::crest-> t==t' && equal_types xrest crest
             in
             let rec search_equal x c=
                 match c with
                 [] -> false
                 | (g,(_,_,c,_,_,_,_,_))::crest ->(if n==g then equal_types x c else false)|| search_equal x crest
             in
             if List.mem_assoc n mmap && search_equal xmap mmap then
               static_error lm "Duplicate method."
             else (
               let rec check_type te =
                 match te with
                   ManifestTypeExpr (_, IntType) -> IntType
                 | ManifestTypeExpr (_, Char) -> Char
                 | ManifestTypeExpr (_, Bool) -> Bool
                 | IdentTypeExpr(lt, cn) ->
                     match search2' cn (pn,ilist) classdeclmap classmap0 with
                       Some s -> ObjType s
                     | None -> match search2' cn (pn,ilist) interfdeclmap interfmap0 with
                         Some s -> ObjType s
                       | None -> static_error lt ("No such class or interface: "^cn)
                 | _ -> static_error (type_expr_loc te) "Invalid return type of this method."
               in
               let check_t t=
                 match t with
                   Some ManifestTypeExpr (_, Void) -> None
                 | Some t-> Some (check_type t)
                 | None -> None
               in
               let rec matchargs xs xs'= (* match the argument list of the method in the interface with the arg list of the method in the class *)
                  match xs with
                  [] -> if xs'=[] then () else static_error lm ("Incorrect number of arguments: "^n)
                  | (an,x)::xs -> match xs' with
                              [] -> static_error lm ("Incorrect number of arguments: "^n)
                              |(an',x')::xs' when an=an'-> expect_type (pn,ilist) lm x x';matchargs xs xs'
                              | _ -> static_error lm ("Arguments must have the same name as in the interface method: "^an)
               in
               let (pre, post) =
                 match co with
                   None -> let rec search_interf i=
                       match i with
                         [] -> static_error lm ("Non-fixpoint function must have contract: "^n)
                         | name::rest -> match try_assoc' (pn,ilist) name interfmap with
                                           None -> search_interf rest
                                          |Some(_,meth_specs,_,_) -> match try_assoc n meth_specs with
                                                                   None -> search_interf rest
                                                                 | Some(_,_, xmap', pre, post,Instance,v)-> matchargs xmap xmap';(pre,post)
                           in
                           search_interf interfs
                 | Some (pre, post) ->
                     let (wpre, tenv) = check_pred (pn,ilist) [] xmap pre in
                     let postmap = match check_t t with None -> tenv | Some rt -> ("result", rt)::tenv in
                     let (wpost, _) = check_pred (pn,ilist) [] postmap post in
                     (wpre, wpost)
               in
               (if n="main" then
                 match pre with ExprPred(lp,pre) -> match post with ExprPred(lp',post) ->
                   match pre with 
                     True(_) -> 
                       match post with
                         True(_) -> main_meth:=(cn,l)::!main_meth
                       | _ -> static_error lp' "The postcondition of the main method must be 'true'" 
                   | _ -> static_error lp "The precondition of the main method must be 'true'"
                );
               iter ((n, (lm,check_t t, xmap, pre, post, ss,fb,v))::mmap) meths
            )
         in
          begin
           match meths_opt with
             meths -> iter [] meths
           | [] -> (cn, (l,None,fds,constr,super,interfs,pn,ilist))
         end
      )
      classfmap
  in
  let classmap1 = if file_type path<>Java then [] else
    List.map
      (fun (cn, (l,meths, fds,constr_opt,super,interfs,pn,ilist)) ->
         let rec iter cmap constr =
           match constr with
             [] -> (cn, (l,meths,fds,Some (List.rev cmap),super,interfs,pn,ilist))
             | Cons (lm,ps, co, ss,v)::constr ->
               let xmap =
                 let rec iter xm xs =
                   match xs with
                    [] -> List.rev xm
                  | (te, x)::xs -> if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
                      let t = check_pure_type (pn,ilist) [] te in
                      iter ((x, t)::xm) xs
                 in
                 iter [] ps
               in
               let rec equal_types x c=
                 match x with
                 [] -> List.length c==0
                |(name,t)::xrest -> match c with
                  []-> false
                  | (name',t')::crest-> t==t' && equal_types xrest crest
               in
               let rec search_equal x c=
                 match c with
                 [] -> false
                 | (c,_)::crest ->equal_types x c || search_equal x crest
               in
               if search_equal xmap cmap then
               static_error lm "Duplicate constructor"
               else (
               let (pre, post) =
                 match co with
                   None -> static_error lm "Constructor must have contract: "
                 | Some (pre, post) ->
                     let (wpre, tenv) = check_pred (pn,ilist) [] xmap pre in
                     let postmap = ("result", ObjType(cn))::tenv in
                     let (wpost, _) = check_pred (pn,ilist) [] postmap post in
                     (wpre, wpost)
               in
               iter ((xmap, (lm,pre,post,ss,v))::cmap) constr
               )
         in
         begin
           match constr_opt with
             constr -> iter [] constr
             | [] -> (cn, (l,meths,fds,None,super,interfs,pn,ilist))
         end
      )
      classmethmap
  in
  
  let classmap= 
    let rec iter map0 map1 =
      match map0 with
        [] -> map1
      | (cn, (l0,meths0,fds0,constr0,super0,interfs0,pn0,ilist0)) as elem::rest ->
        match try_assoc cn map1 with
          None -> iter rest (elem::map1)
        | Some (l1,meths1,fds1,constr1,super1,interfs1,pn1,ilist1) ->
          let match_fds fds0 fds1=
            let rec iter fds0 fds1=
            match fds0 with
              [] -> fds1
            | (f0, (lf0,t0,vis0)) as elem::rest ->
              match try_assoc f0 fds1 with
                None-> iter rest (elem::fds1)
              | Some(lf1,t1,vis1) -> if t0<>t1 || vis0<>vis1 then static_error lf1 "Duplicate field"
                else iter rest fds1
            in
            match fds0 with
              None-> fds1
            | Some fds0 -> (match fds1 with None-> Some fds0 | Some fds1 -> Some (iter fds0 fds1))
          in
          let match_meths meths0 meths1=
            let rec iter meths0 meths1=
              match meths0 with
                [] -> meths1
              | (n, (lm0,rt0,xmap0,pre0,post0,ss0,fb0,v0)) as elem::rest ->
                match try_assoc n meths1 with
                  None-> iter rest (elem::meths1)
                | Some(lm1,rt1,xmap1,pre1,post1,ss1,fb1,v1) -> 
                  let cenv0 = List.map (fun (x, t) -> (x, Var (lm0, x, ref (Some LocalVar)))) xmap0 in
                  check_func_header_compat (pn1,ilist1) lm1 "Method implementation check: " (Regular,[],rt1, xmap1,false, pre1, post1) (Regular, [], rt0, xmap0, false, cenv0, pre0, post0);
                  if ss0=None then meths_impl:=(n,lm0)::!meths_impl;
                  iter rest meths1
            in
            match meths0 with
              None-> meths1
            | Some meths0 -> match meths1 with None-> Some meths0 | Some meths1 -> Some (iter meths0 meths1)
          in
          let match_constr constr0 constr1=
            let rec iter constr0 constr1=
              match constr0 with
                [] -> constr1
              | (xmap0, (lm0,pre0,post0,ss0,v0)) as elem::rest ->
                match try_assoc xmap0 constr1 with
                  None-> iter rest (elem::constr1)
                | Some(lm1,pre1,post1,ss1,v1) ->
                  let cenv0 = List.map (fun (x, t) -> (x, Var (lm0, x, ref (Some LocalVar)))) xmap0 in
                  let rt= Some (ObjType(cn)) in
                  check_func_header_compat (pn1,ilist1) lm1 "Constructor implementation check: " (Regular,[],rt, xmap0,false, pre1, post1) (Regular, [], rt, xmap0, false, cenv0, pre0, post0);
                  if ss0=None then cons_impl:=(cn,lm0)::!cons_impl;
                  iter rest constr1
            in
            match constr0 with
              None-> constr1
            | Some constr0 -> match constr1 with None-> Some constr0 | Some constr1 -> Some (iter constr0 constr1)
          in
          if super0<>super1 || interfs0<>interfs1 then static_error l1 "Duplicate class"
          else 
          let meths'= match_meths meths0 meths1 in
          let fds'= match_fds fds0 fds1 in
          let constr'= match_constr constr0 constr1 in
          iter rest ((cn,(l1,meths',fds',constr',super1,interfs1,pn1,ilist1))::map1)
    in
    iter classmap0 classmap1
  in
  
  
  let _=
  if file_type path=Java then
    let rec check_spec_lemmas lemmas impl=
      match lemmas with
        [] when List.length impl=0-> ()
      | Func(l,Lemma,tparams,rt,fn,arglist,atomic,ftype,contract,None,fb,vis)::rest ->
          if List.mem (fn,l) impl then
            let impl'= remove (fun (x,l0) -> x=fn && l=l0) impl in
            check_spec_lemmas rest impl'
          else
            static_error l "No implementation found for this lemma."
    in
    check_spec_lemmas !spec_lemmas prototypes_implemented
  else
    ()
  in
  
  let _=
  if file_type path=Java then
    let rec check_spec_classes classes meths_impl cons_impl=
      match classes with
        [] -> (match meths_impl with
            []-> ()
          | (n,lm0)::_ -> static_error lm0 ("Method not in specs: "^n)
          )
      | Class(l,cn,meths,fds,cons,super,inames)::rest ->
          let check_meths meths meths_impl=
            let rec iter mlist meths_impl=
              match mlist with
                [] -> meths_impl
              | Meth(lm,rt,n,ps,co,None,fb,v) as elem::rest ->
                if List.mem (n,lm) meths_impl then
                  let meths_impl'= remove (fun (x,l0) -> x=n && lm=l0) meths_impl in
                  iter rest meths_impl'
                else
                static_error lm "No implementation found for this method."
            in
            iter meths meths_impl
          in
          let check_cons cons cons_impl=
            let rec iter clist cons_impl=
              match clist with
                [] -> cons_impl
              | Cons (lm,ps, co,None,v) as elem::rest ->
                if List.mem (cn,lm) cons_impl then
                  let cons_impl'= remove (fun (x,l0) -> x=cn && lm=l0) cons_impl in
                  iter rest cons_impl'
                else
                static_error lm "No implementation found for this constructor."
            in
            iter cons cons_impl
          in
          check_spec_classes rest (check_meths meths meths_impl) (check_cons cons cons_impl)
    in
    check_spec_classes !spec_classes !meths_impl !cons_impl
  else
    ()
  in
  
  let nonempty_pred_symbs = List.map (fun (_, (_, (_, _, _, symb, _))) -> symb) field_pred_map in
  
  let check_breakpoint h env ((((basepath, relpath), line, col), _) as l) =
    match breakpoint with
      None -> ()
    | Some (path0, line0) ->
      if line = line0 && Filename.concat basepath relpath = path0 then
        assert_false h env l "Breakpoint reached."
  in
  
  let check_leaks h env l msg =
    match file_type path with
    Java -> check_breakpoint h env l
    | _ -> let (_, _, _, chars_symb, _) = List.assoc "chars" predfammap in
    let (_, _, _, string_literal_symb, _) = List.assoc "string_literal" predfammap in
    let (stringlitchunks, otherchunks) =
      let rec iter stringlitchunks otherchunks h =
        match h with
          [] -> (stringlitchunks, otherchunks)
        | (((g, true), coef, ts, _) as chunk)::h when g == string_literal_symb && (file_type path) <> Java -> iter (chunk::stringlitchunks) otherchunks h
        | chunk::h -> iter stringlitchunks (chunk::otherchunks) h
      in
      iter [] [] h
    in
    let rec iter stringlitchunks otherchunks =
      match stringlitchunks with
        [] ->
        with_context (Executing (otherchunks, env, l, "Leak check.")) (fun _ -> 
          if otherchunks = [] then
            check_breakpoint [] env l
          else
            assert_false otherchunks env l msg
        )
      | (_, coef, [arr; cs], _)::stringlitchunks ->
        let rec consume_chars_chunk otherchunks h =
          match h with
            [] -> assert_false h env l "At function exit: string_literal chunk without matching chars chunk."
          | ((g, true), coef', [arr'; cs'], _)::h when g == chars_symb && (file_type path) <> Java && definitely_equal coef coef' && definitely_equal arr arr' && definitely_equal cs cs' -> iter stringlitchunks (otherchunks @ h)
          | chunk::h -> consume_chars_chunk (chunk::otherchunks) h
        in
        consume_chars_chunk [] otherchunks
    in
    with_context (Executing (h, env, l, "Cleaning up string literal chunks.")) (fun _ -> iter stringlitchunks otherchunks)
  in 
  let eval_non_pure (pn,ilist) is_ghost_expr h env e =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg -> assert_term t h env l msg) in
    eval_core (pn,ilist) assert_term (Some ((fun l t f -> read_field h env l t f), (fun l p t -> deref_pointer h env l p t))) env e
  in 
  
  let eval_h (pn,ilist) is_ghost_expr h env e cont =
    match e with
      StringLit (l, s)->( match file_type path with
        Java ->
          let value = get_unique_var_symb "stringLiteral" (ObjType "String") in
          assume_neq value (ctxt#mk_intlit 0) 
          (fun()-> cont h value)
      | _ ->
          let (_, _, _, chars_symb, _) = List.assoc "chars" predfammap in
          let (_, _, _, string_literal_symb, _) = List.assoc "string_literal" predfammap in
          let (_, _, _, _, chars_contains_symb) = List.assoc "chars_contains" purefuncmap in
          let value = get_unique_var_symb "stringLiteral" (PtrType Char) in
          let cs = get_unique_var_symb "stringLiteralChars" (InductiveType ("chars", [])) in
          let coef = get_unique_var_symb "stringLiteralCoef" RealType in
            assume (ctxt#mk_app chars_contains_symb [cs; ctxt#mk_intlit 0]) (fun () -> (* chars_contains(cs, 0) == true *)
              assume (ctxt#mk_not (ctxt#mk_eq value (ctxt#mk_intlit 0))) (fun () ->
                cont (((chars_symb, true), coef, [value; cs], None)::((string_literal_symb, true), coef, [value; cs], None)::h) value
              )
            )
	  )
    | e -> cont h (eval_non_pure (pn,ilist) is_ghost_expr h env e)
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
  
  let rec verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env s tcont return_cont =
    stats#stmtExec;
    let l = stmt_loc s in
    if verbose then print_endline (string_of_loc l ^ ": Executing statement");
    check_breakpoint h env l;
    let eval0 = eval (pn,ilist) in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure (pn,ilist) pure h env e in
    let eval_h0 = eval_h (pn,ilist) in
    let eval_h h env e cont = if not pure then check_ghost ghostenv l e; eval_h (pn,ilist) pure h env e cont in
    let rec evhs h env es cont =
      match es with
        [] -> cont h []
      | e::es -> eval_h h env e (fun h v -> evhs h env es (fun h vs -> cont h (v::vs)))
    in 
    let ev e = eval env e in
    let cont= tcont sizemap tenv ghostenv
    in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context."
    in
    let vartp l x = match try_assoc x tenv with None -> static_error l ("No such variable: "^x) | Some tp -> tp in
    let check_correct xo g targs pats (lg, callee_tparams, tr, ps, pre, post, body,v)=
      let targs =
        if callee_tparams <> [] && targs = [] then
          List.map (fun _ -> InferredType (ref None)) callee_tparams
        else
          List.map (check_pure_type (pn,ilist) tparams) targs
      in
      let tpenv =
        match zip callee_tparams targs with
          None -> static_error l "Incorrect number of type arguments."
        | Some tpenv -> tpenv
      in
      let ys = List.map (function (p, t) -> p) ps in
        let ws =
          match zip pats ps with
            None -> static_error l "Incorrect number of arguments."
          | Some bs ->
            List.map
              (function (LitPat e, (x, t0)) ->
                 let t = instantiate_type tpenv t0 in
                 box (check_expr_t (pn,ilist) tparams tenv e t) t t0
              ) bs
        in
        evhs h env ws (fun h ts ->
        let Some env' = zip ys ts in
        let cenv = env' in
        with_context PushSubcontext (fun () ->
          assert_pred (pn,ilist) h ghostenv cenv pre real_unit (fun h ghostenv' env' chunk_size ->
            let _ =
              match leminfo with
                None -> ()
              | Some (lems, g0, indinfo) ->
                  if match g with Some g -> List.mem g lems | None -> true then
                    ()
                  else 
                      if g = Some g0 then
                        let rec nonempty h =
                          match h with
                            [] -> false
                          | ((p, true), coef, ts, _)::_ when List.memq p nonempty_pred_symbs && coef == real_unit -> true
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
            let r =
              match tr with
                None -> None
              | Some t ->
                let symbol_name =
                  match xo with
                    None -> "result"
                  | Some x -> x
                in
                Some (get_unique_var_symb symbol_name t, t)
            in
            let env'' = match r with None -> env' | Some (r, t) -> update env' "result" r in
            assume_pred (pn,ilist) h ghostenv' env'' post real_unit None None (fun h _ _ ->
              let env =
                match xo with
                  None -> env
                | Some x ->
                  let tpx = vartp l x in
                  let _ = check_assign l x in
                    begin
                      match r with
                        None -> static_error l "Call does not return a result."
                      | Some (r, t) -> expect_type (pn,ilist) l t tpx; update env x r
                    end
              in
              match g with
                Some g when (startswith g "new ") -> 
                  let cn= match (search' (String.sub g 4 ((String.length g)-4)) (pn,ilist) class_symbols) with Some s -> s in
                  assume_neq (List.assoc (match xo with Some xo->xo) env) (ctxt#mk_intlit 0) (fun () ->
                  assume_eq (ctxt#mk_app get_class_symbol [(List.assoc (match xo with Some xo->xo) env)]) (ctxt#mk_app (List.assoc cn class_symbols) [])(fun () -> with_context PopSubcontext (fun () -> cont h env)))
              | _ -> with_context PopSubcontext (fun () -> cont h env)
            )
          )
        )
        )
    in
    let call_stmt l xo g targs pats fb=
      match file_type path with
      Java ->
      (
        let (class_name,fb,pats,iscons)= 
          (if fb=Static then 
            (if startswith g "new " then
               let id=(String.sub g 4 ((String.length g)-4)) in
               let cn= match search' id (pn,ilist) classmap with Some s ->s | None -> static_error l ("Constructor wasn't found: "^id) in
               (cn,Static,pats,true)
            else ("",Static,pats,false)
            )
           else(
             if (match pats with LitPat(Var(_,cn,_))::_->(search cn (pn,ilist) classmap) |_->false)
               then match pats with LitPat(Var(_,cn,_))::rest->(cn,Static,rest,false)
             else
               match List.hd pats with LitPat (Var(_,x,_)) ->( match vartp l x with (* HACK :) this is altijd 1e argument bij instance method*) ObjType(class_name)->(class_name,Instance,pats,false))
            )
           )
        in
        match try_assoc' (pn,ilist) class_name classmap with
          Some(_,Some methmap,_,Some consmap,super,interfs,pn,ilist) -> 
            (if pure then 
               static_error l "Cannot call methods in a pure context."
             else
             let rec search_meth mmap=
               match mmap with
                 [] -> static_error l ("Method "^g^" not found!")
               | (n,(lm,rt, xmap, pre, post, body,fbm,v))::rest when n=g-> 
                 let match_args xmap pats =
                   match zip pats xmap with
                     None -> false
                   | Some bs ->
                       try List.map(function (LitPat e, (x, tp)) -> check_expr_t (pn,ilist) [] tenv e tp) bs; true
                       with StaticError (l, msg) -> false
                 in
                 if(match_args xmap pats) then
                   if fb <>fbm then static_error l ("Wrong method binding of "^g^" :"^(tostring fb)^" instead of"^(tostring fbm))
                   else check_correct xo (Some g) targs pats (lm, [], rt, xmap, pre, post, body,v)
                 else
                   search_meth rest
               | _::rest -> search_meth rest
             in
             let rec search_cons clist=
               match clist with
                [] -> static_error l ("Constructor "^g^" not found!")
              | (xmap,(lm,pre,post,ss,v))::rest->
                let match_args xmap pats =
                  match zip pats xmap with
                    None -> false
                  | Some bs -> 
                      try List.map(function (LitPat e, (x, tp)) -> check_expr_t (pn,ilist) [] tenv e tp) bs; true
                      with StaticError (l, msg) -> false
                in
                if(match_args xmap pats) then
                  check_correct xo (Some g) targs pats (lm, [],Some (ObjType(class_name)), xmap, pre, post,ss,Static)
                else search_cons rest
              in
              if iscons then 
                search_cons consmap
              else 
                search_meth methmap
            )
        | None ->
           (match try_assoc' (pn,ilist) class_name interfmap with
              Some(_,methmap,pn,ilist) -> 
                (match try_assoc g methmap with
                   Some(lm,rt, xmap, pre, post,fbm,v) ->
                    if fb <>fbm 
                      then static_error l ("Wrong function binding of "^g^" :"^(tostring fb)^" instead of"^(tostring fbm));
                      let _ = if pure then static_error l "Cannot call regular functions in a pure context." in
                      check_correct xo (Some g) targs pats (lm, [], rt, xmap, pre, post, None,v)
                 | None->  static_error l ("Method "^class_name^" not found!!")
                )
            | None ->
                (match try_assoc' (pn,ilist) g funcmap with (* java probleem*)
                   None -> 
                     (match try_assoc' (pn,ilist) g purefuncmap with
                        None -> static_error l ("No such method: " ^ g)
                      | Some (lg, callee_tparams, rt, pts, gs) ->
                        (match xo with
                           None -> static_error l "Cannot write call of pure function as statement."
                         | Some x ->
                             let tpx = vartp l x in
                             let Some g=search' g (pn,ilist) purefuncmap in
                             let w = check_expr_t (pn,ilist) tparams tenv (CallExpr (l, g, targs, [], pats,fb)) tpx in
                             let _ = check_assign l x in
                             cont h (update env x (ev w))
                        )
                     )
                 | Some (lg, k, tparams, tr, ps, atomic, pre, pre_tenv, post, body,fbf,v) ->
                     let g= match search' g (pn,ilist) funcmap with Some s -> s in
                     if fb <>fbf then static_error l ("Wrong function binding "^(tostring fb)^" instead of "^(tostring fbf));
                     if body = None then register_prototype_used lg g;
                     let _ = if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." in
                     let _ = if not pure && k = Lemma then static_error l "Cannot call lemma functions in a non-pure context."        in
                     check_correct xo (Some g) targs pats (lg, tparams, tr, ps, pre, post, body,v)
                )
            )
      )
    | _ ->
      (
      match try_assoc g tenv with
        Some (PtrType (FuncType ftn)) ->
        let fterm = List.assoc g env in
        let (lg, _, _, _, isfuncsymb) = List.assoc ("is_" ^ ftn) purefuncmap in
        let phi = ctxt#mk_app isfuncsymb [fterm] in
        assert_term phi h env l ("Could not prove " ^ ctxt#pprint phi); (* TODO: Evaluate error message lazily. *)
        let (_, gh, rt, xmap, pre, post) = List.assoc ftn functypemap in
        if pure && gh = Real then static_error l "Cannot call function pointer in a pure context.";
        check_correct xo None [] (LitPat (Var (dummy_loc, g, ref (Some LocalVar)))::pats) (lg, [], rt, (("this", PtrType Void)::xmap), pre, post, None, Public)
      | _ ->
      match try_assoc' (pn,ilist) g funcmap with
        None -> (
        match try_assoc' (pn,ilist) g purefuncmap with
          None -> static_error l ("No such function: " ^ g)
        | Some (lg, callee_tparams, rt, pts, gs) -> (
          match xo with
            None -> static_error l "Cannot write call of pure function as statement."
          | Some x ->
            let tpx = vartp l x in
            let w = check_expr_t (pn,ilist) tparams tenv (CallExpr (l, g, targs, [], pats,fb)) tpx in
            let _ = check_assign l x in
            cont h (update env x (ev w))
          )
        )
      | Some (lg,k, tparams, tr, ps, atomic, pre, pre_tenv, post, body,fbf,v) ->
        if fb <>fbf then static_error l ("Wrong function binding "^(tostring fb)^" instead of "^(tostring fbf));
        if body = None then register_prototype_used lg g;
        let _ = if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." in
        let _ = if not pure && k = Lemma then static_error l "Cannot call lemma functions in a non-pure context." in
        check_correct xo (Some g) targs pats (lg, tparams, tr, ps, pre, post, body,v)
      ) 
    in 
    match s with
      NonpureStmt (l, allowed, s) ->
      if allowed then
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes false leminfo sizemap tenv ghostenv h env s tcont return_cont
      else
        static_error l "Non-pure statements are not allowed here."
    | Assign (l, x, CallExpr (lc, "malloc", [], [], args,Static)) ->
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
          let result = get_unique_var_symb x tpx in
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
                     let (_, (_, _, _, malloc_block_symb, _)) = (List.assoc tn malloc_block_pred_map)in
                     cont (h @ [((malloc_block_symb, true), real_unit, [result], None)]) (update env x result)
                   | (f, (lf, gh, t))::fds ->
                     let fref = new fieldref f in
                     fref#set_parent tn; fref#set_range t; assume_field h fref result (get_unique_var_symb "value" t) real_unit (fun h -> iter h fds)
                 in
                 iter h fds
               )
            )
        | _ -> call_stmt l (Some x) "malloc" [] args Static
      end
    | CallStmt (l, "assume_is_int", [], [Var (lv, x, _) as e],Static) ->
      if not pure then static_error l "This function may be called only from a pure context.";
      if List.mem x ghostenv then static_error l "The argument for this call must be a non-ghost variable.";
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      assume_is_of_type (ev w) tp (fun () -> cont h env)
    | CallStmt (l, "assume_class_this", [], [],Instance) when file_type path=Java && List.mem_assoc "this" env->
    let classname= match vartp l "this" with ObjType cn -> cn in
      assume_eq (ctxt#mk_app get_class_symbol [List.assoc "this" env]) (ctxt#mk_app (List.assoc classname class_symbols) [])(fun () ->cont h env)
    | CallStmt (l, "free", [], args,Static) ->
      begin
        match List.map (check_expr (pn,ilist) tparams tenv) args with
          [(arg, PtrType (StructType tn))] ->
          let _ = if pure then static_error l "Cannot call a non-pure function from a pure context." in
          let fds =
            let ds=match ps with[PackageDecl(_,"",[],ds)] -> ds in
            match flatmap (function (Struct (ls, sn, Some fds)) when sn = tn -> [fds] | _ -> []) ds with
              [fds] -> fds
            | [] -> static_error l "Freeing an object of a struct type declared without a body is not supported."
          in
          let arg = ev arg in
          let rec iter h fds =
            match fds with
              [] -> cont h env
            | (Field (lf, _, t, f,Instance,Public))::fds ->
              let fref = new fieldref f in
              fref#set_parent tn;
              get_field (pn,ilist) h arg fref l (fun h coef _ -> if not (definitely_equal coef real_unit) then assert_false h env l "Free requires full field chunk permissions."; iter h fds)
          in
          let (_, (_, _, _, malloc_block_symb, _)) = (List.assoc tn malloc_block_pred_map)in
          assert_chunk (pn,ilist)  h [] [("x", arg)] l (malloc_block_symb, true) real_unit DummyPat [LitPat (Var (l, "x", ref (Some LocalVar)))] (fun h coef _ _ _ _ -> if not (definitely_equal coef real_unit) then assert_false h env l "Free requires full malloc_block permission."; iter h fds)
        | _ -> call_stmt l None "free" [] (List.map (fun e -> LitPat e) args) Static
      end
    | Assign (l, x, CallExpr (lc, g, targs, [], pats,fb)) ->
      call_stmt l (Some x) g targs pats fb
    | Assign (l, x, e) -> 
      let tpx = vartp l x in
      let w = check_expr_t (pn,ilist) tparams tenv e tpx in
      let _ = check_assign l x in
      eval_h h env w (fun h v -> cont h ((x, v)::env));
    | DeclStmt (l, te, x, e) ->
      if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.");
      let t = check_pure_type (pn,ilist) tparams te in
      let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap ((x, t)::tenv) ghostenv h env (Assign (l, x, e)) tcont return_cont (* BUGBUG: e should be typechecked outside of the scope of x *)
      ;
    | Write (l, e, f, rhs) ->
      let (w, tp) = check_deref true pure (pn,ilist) l tparams tenv e f in
      let wrhs = check_expr_t (pn,ilist) tparams tenv rhs tp in
      eval_h h env w (fun h t ->
        let (_, (_, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
        get_field (pn,ilist) h t f l (fun h coef _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a field requires full field permission.";
          cont (((f_symb, true), real_unit, [t; ev wrhs], None)::h) env)
      )
    | WriteDeref (l, e, rhs) ->
      if pure then static_error l "Cannot write in a pure context.";
      let (w, pointerType) = check_expr (pn,ilist) tparams tenv e in
      let pointeeType = 
        match pointerType with
          PtrType t -> t
        | _ -> static_error l "Operand of dereference must be pointer."
      in
      let wrhs = check_expr_t (pn,ilist) tparams tenv rhs pointeeType in
      eval_h h env w (fun h t ->
        let predSymb = pointee_pred_symb l pointeeType in
        get_points_to (pn,ilist) h t predSymb l (fun h coef _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a memory location requires full permission.";
          cont (((predSymb, true), real_unit, [t; ev wrhs], None)::h) env)
      )
    | CallStmt (l, g, targs, es,fb) ->
      call_stmt l None g targs (List.map (fun e -> LitPat e) es) fb
    | IfStmt (l, e, ss1, ss2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      branch
        (fun _ -> assume (ev w) (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss1 tcont return_cont))
        (fun _ -> assume (ctxt#mk_not (ev w)) (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss2 tcont return_cont))
    | SwitchStmt (l, e, cs) ->
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let (tn, targs, Some (_, tparams, ctormap)) =
        match tp with
          InductiveType (i, targs) -> (i, targs, try_assoc' (pn,ilist) i inductivemap)
        | _ -> static_error l "Switch statement operand is not an inductive value."
      in
      let (Some tpenv) = zip tparams targs in
      let t = ev w in
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
            match try_assoc' (pn,ilist) cn ctormap with
              None -> static_error lc ("Not a constructor of type " ^ tn)
            | Some (l, pts) -> pts
          in
		  let Some cn= search' cn (pn,ilist) ctormap in
          let _ = if not (List.mem cn ctors) then static_error lc "Constructor already handled in earlier clause." in
          let (ptenv, xterms, xenv) =
            let rec iter ptenv xterms xenv pats pts =
              match (pats, pts) with
                ([], []) -> (List.rev ptenv, List.rev xterms, List.rev xenv)
              | (pat::pats, tp::pts) ->
                if List.mem_assoc pat tenv then static_error lc ("Pattern variable '" ^ pat ^ "' hides existing local variable '" ^ pat ^ "'.");
                if List.mem_assoc pat ptenv then static_error lc "Duplicate pattern variable.";
                let tp' = instantiate_type tpenv tp in
                let term = get_unique_var_symb pat tp' in
                let term' =
                  match tp with
                    TypeParam x -> convert_provertype term (provertype_of_type tp') ProverInductive (pn,ilist)
                  | _ -> term
                in
                iter ((pat, tp')::ptenv) (term'::xterms) ((pat, term)::xenv) pats pts
              | ([], _) -> static_error lc "Too few arguments."
              | _ -> static_error lc "Too many arguments."
            in
            iter [] [] [] pats pts
          in
          let Some (_, _, _, _, ctorsym) = try_assoc' (pn,ilist) cn purefuncmap in
          let sizemap =
            match try_assq t sizemap with
              None -> sizemap
            | Some k -> List.map (fun (x, t) -> (t, k - 1)) xenv @ sizemap
          in
          branch
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym xterms) (fun _ -> verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap (ptenv @ tenv) (pats @ ghostenv) h (xenv @ env) ss tcont return_cont))
            (fun _ -> iter (List.filter (function cn' -> cn' <> cn) ctors) cs)
      in
      iter (List.map (function (cn, _) -> cn) ctormap) cs
    | Assert (l, p) ->
      let (wp, tenv) = check_pred (pn,ilist) tparams tenv p in
      assert_pred (pn,ilist) h ghostenv env wp real_unit (fun _ ghostenv env _ ->
        tcont sizemap tenv ghostenv h env
      )
    | Leak (l, p) ->
      let (wp, tenv) = check_pred (pn,ilist) tparams tenv p in
      assert_pred (pn,ilist) h ghostenv env wp real_unit (fun h ghostenv env size ->
        tcont sizemap tenv ghostenv h env
      )
    | Open (l, g, pats0, pats, coefpat) ->
      let (g_symb, pats0, dropcount, ps, env0, p) =
        match try_assoc' (pn,ilist) g predfammap with
          Some (_, _, _, g_symb, _) ->
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x))-> (l,x) | _ -> static_error l "Predicate family indices must be class names.") pats0)
          | _ -> check_funcnamelist (List.map (function LitPat (Var (l, x, _)) -> (l, x) | _ -> static_error l "Predicate family indices must be function names.") pats0)
          in
          begin
            match file_type path with
            Java->
              (match try_assoc_pair' (pn,ilist) (g, fns) predinstmap with
                Some (_, ps, _, p) ->
                ((g_symb, true), List.map (fun fn -> LitPat (ClassLit(l,fn))) fns, List.length fns, ps, [], p)
              | None -> static_error l ("No such predicate instance: "^g))
            |_ ->
              (match try_assoc_pair' (pn,ilist) (g, fns) predinstmap with
                Some (_, ps, _, p) ->
                ((g_symb, true), List.map (fun fn -> LitPat (FuncNameExpr fn)) fns, List.length fns, ps, [], p)
              | None -> static_error l "No such predicate instance.")
          end
        | None ->
          begin
          match try_assoc' (pn,ilist) g predctormap with
            None -> static_error l "No such predicate or predicate constructor."
          | Some (_, ps1, ps2, body, funcsym) ->
            let bs0 =
              match zip pats0 ps1 with
                None -> static_error l "Incorrect number of predicate constructor arguments."
              | Some bs ->
                List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions.") bs
            in
            let g_symb = ctxt#mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
            ((g_symb, false), [], 0, ps2, bs0, body)
          end
      in
      let (coefpat, tenv) = match coefpat with None -> (DummyPat, tenv) | Some coefpat -> check_pat (pn,ilist) l tparams tenv RealType coefpat in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv (List.map (fun (x, t) -> t) ps) pats in
      let pats = pats0 @ wpats in
      assert_chunk (pn,ilist) h ghostenv env l g_symb real_unit coefpat pats (fun h coef ts chunk_size ghostenv env ->
        let ts = drop dropcount ts in
        let ys = List.map (function (p, t) -> p) ps in
        let Some env' = zip ys ts in
        let env' = env0 @ env' in
        let body_size = match chunk_size with None -> None | Some k -> Some (k - 1) in
        with_context PushSubcontext (fun () ->
          assume_pred (pn,ilist) h ghostenv env' p coef body_size body_size (fun h _ _ ->
            with_context PopSubcontext (fun () -> tcont sizemap tenv' ghostenv h env)
          )
        )
      )
    | SplitFractionStmt (l, p, pats, coefopt) ->
      let (g_symb, pts) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate."
        | Some (_, arity, pts, g_symb, _) ->
          if arity <> 0 then static_error l "Predicate families are not supported in split_fraction statements.";
          ((g_symb, true), pts)
      in
      let splitcoef =
        match coefopt with
          None -> real_half
        | Some e ->
          let w = check_expr_t (pn,ilist) tparams tenv e RealType in
          let coef = ev w in
          assert_term (ctxt#mk_real_lt real_zero coef) h env l "Split coefficient must be positive.";
          assert_term (ctxt#mk_real_lt coef real_unit) h env l "Split coefficient must be less than one.";
          coef
      in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      assert_chunk (pn,ilist) h ghostenv env l g_symb real_unit DummyPat wpats (fun h coef ts chunk_size ghostenv env ->
        let coef1 = ctxt#mk_real_mul splitcoef coef in
        let coef2 = ctxt#mk_real_mul (ctxt#mk_real_sub real_unit splitcoef) coef in
        let h = (g_symb, coef1, ts, None)::(g_symb, coef2, ts, None)::h in
        tcont sizemap tenv' ghostenv h env
      )
    | MergeFractionsStmt (l, p, pats) ->
      let (g_symb, pts, inputParamCount) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate."
        | Some (_, arity, pts, g_symb, inputParamCount) ->
          if arity <> 0 then static_error l "Predicate families are not supported in merge_fractions statements.";
          begin
            match inputParamCount with
              None ->
              static_error l
                ("Cannot merge this predicate: it is not declared precise. "
                 ^ "To declare a predicate precise, separate the input parameters "
                 ^ "from the output parameters using a semicolon in the predicate declaration.");
            | Some n -> ((g_symb, true), pts, n)
          end
      in
      let (pats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      let (inpats, outpats) = take_drop inputParamCount pats in
      List.iter (function (LitPat e) -> () | _ -> static_error l "No patterns allowed at input positions.") inpats;
      assert_chunk (pn,ilist) h ghostenv env l g_symb real_unit DummyPat pats (fun h coef1 ts1 _ ghostenv env ->
        assert_chunk (pn,ilist) h ghostenv env l g_symb real_unit DummyPat pats (fun h coef2 ts2 _ _ _ ->
          let (Some tpairs) = zip ts1 ts2 in
          let (ints, outts) = take_drop inputParamCount tpairs in
          let merged_chunk = (g_symb, ctxt#mk_real_add coef1 coef2, ts1, None) in
          let h = merged_chunk::h in
          let rec iter outts =
            match outts with
              [] -> tcont sizemap tenv' ghostenv h env
            | (t1, t2)::ts ->
              assume (ctxt#mk_eq t1 t2) (fun () -> iter ts)
          in
          iter outts
        )
      )
    | DisposeBoxStmt (l, bcn, pats, handleClauses) ->
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' (pn,ilist) bcn boxmap with
          None -> static_error l "No such box class."
        | Some boxinfo -> boxinfo
      in
      let Some (_, _, pts, g_symb, _) = try_assoc' (pn,ilist) bcn predfammap in
      let (pats, tenv) = check_pats (pn,ilist) l tparams tenv pts pats in
      assert_chunk (pn,ilist) h ghostenv env l (g_symb, true) real_unit DummyPat pats $. fun h coef ts _ ghostenv env ->
      if not (definitely_equal coef real_unit) then static_error l "Disposing a box requires full permission.";
      let boxId::argts = ts in
      let Some boxArgMap = zip boxpmap argts in
      let boxArgMap = List.map (fun ((x, _), t) -> (x, t)) boxArgMap in
      with_context PushSubcontext $. fun () ->
      assume_pred (pn,ilist) h ghostenv boxArgMap inv real_unit None None $. fun h _ boxVarMap ->
      let rec dispose_handles tenv ghostenv h env handleClauses cont =
        match handleClauses with
          [] -> cont tenv ghostenv h env
        | (l, hpn, pats)::handleClauses ->
          begin
            match try_assoc hpn hpmap with
              None -> static_error l "No such handle predicate."
            | Some (lhp, hpParamMap, hpInv, pbcs) ->
              let hpParamTypes = List.map (fun (x, t) -> t) hpParamMap in
              let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv (HandleIdType::hpParamTypes) pats in
              let Some (_, _, _, hpn_symb, _) = try_assoc' (pn,ilist) hpn predfammap in
              let handlePat::argPats = wpats in
              let pats = handlePat::LitPat (Var (l, "#boxId", ref (Some LocalVar)))::argPats in
              assert_chunk (pn,ilist) h ghostenv (("#boxId", boxId)::env) l (hpn_symb, true) real_unit DummyPat pats $. fun h coef ts _ ghostenv env ->
              if not (definitely_equal coef real_unit) then static_error l "Disposing a handle predicate requires full permission.";
              let env = List.filter (fun (x, t) -> x <> "#boxId") env in
              let handleId::_::hpArgs = ts in
              let Some hpArgMap = zip (List.map (fun (x, t) -> x) hpParamMap) hpArgs in
              let hpInvEnv = [("predicateHandle", handleId)] @ hpArgMap @ boxVarMap in
              assume (eval hpInvEnv hpInv) $. fun () ->
              dispose_handles tenv ghostenv h env handleClauses cont
          end
      in
      dispose_handles tenv ghostenv h env handleClauses $. fun tenv ghostenv h env ->
      with_context PopSubcontext $. fun () ->
      tcont sizemap tenv ghostenv h env
    | Close (l, g, pats0, pats, coef) ->  
      let (ps, bs0, g_symb, p, ts0) =
        match try_assoc' (pn,ilist) g predfammap with
          Some (_, _, _, g_symb, inputParamCount) -> 
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x)) -> (l, x) | _ -> static_error l "Predicate family indices must be class names.") pats0)
          | _ -> check_funcnamelist (List.map (function LitPat (Var (l, x, _)) -> (l, x) | _ -> static_error l "Predicate family indices must be function names.") pats0)
          in
          begin
          match try_assoc_pair' (pn,ilist) (g, fns) predinstmap with
            Some (l, ps, inputParamCount, body) ->
            let ts0 = match file_type path with
              Java -> List.map(fun cn -> 
                let symb= match (search' cn (pn,ilist) class_symbols) with Some s -> s in
                ctxt#mk_app (List.assoc symb class_symbols) []) fns
            | _ -> List.map (fun fn -> (List.assoc fn funcnameterms)) fns in
            (ps, [], (g_symb, true), body, ts0)
          | None -> static_error l "No such predicate instance."
          end
        | None ->
          begin
            match try_assoc' (pn,ilist) g predctormap with
              None -> static_error l ("No such predicate family instance or predicate constructor: "^g)
            | Some (_, ps1, ps2, body, funcsym) ->
              let bs0 =
                match zip pats0 ps1 with
                  None -> static_error l "Incorrect number of predicate constructor arguments."
                | Some bs ->
                  List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions.") bs
              in
              let g_symb = ctxt#mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
              (ps2, bs0, (g_symb, false), body, [])
          end
      in
      let ws =
        match zip pats ps with
          None -> static_error l "Wrong number of arguments."
        | Some bs ->
          List.map (function (LitPat e, (_, tp)) -> check_expr_t (pn,ilist) tparams tenv e tp | pat -> static_error l "Close statement arguments cannot be patterns.") bs
      in
      let ts = List.map ev ws in
      let coef = match coef with None -> real_unit | Some (LitPat coef) -> let coef = check_expr_t (pn,ilist) tparams tenv coef RealType in ev coef | _ -> static_error l "Coefficient in close statement must be expression." in
      let ys = List.map (function (p, t) -> p) ps in
      let Some env' = zip ys ts in
      let env' = bs0 @ env' in
      with_context PushSubcontext (fun () ->
        assert_pred (pn,ilist) h ghostenv env' p coef (fun h _ _ _ ->
          with_context PopSubcontext (fun () -> cont ((g_symb, coef, ts0 @ ts, None)::h) env)
        )
      )
    | CreateBoxStmt (l, x, bcn, args, handleClauses) ->
      if not pure then static_error l "Box creation statements are allowed only in a pure context.";
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' (pn,ilist) bcn boxmap with
          None -> static_error l "No such box class."
        | Some boxinfo -> boxinfo
      in
      let (tenv, ghostenv, env) =
        let rec iter tenv ghostenv env handleClauses =
          match handleClauses with
            [] -> (tenv, ghostenv, env)
          | (l, x, hpn, args)::handleClauses ->
            if List.mem_assoc x tenv then static_error l "Declaration hides existing variable.";
            iter ((x, HandleIdType)::tenv) (x::ghostenv) ((x, get_unique_var_symb x HandleIdType)::env) handleClauses
        in
        iter tenv ghostenv env handleClauses
      in
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable.";
      let boxArgMap =
        match zip args boxpmap with
          None -> static_error l "Incorrect number of arguments."
        | Some bs ->
          List.map
            begin
              fun (e, (pn, pt)) ->
                let w = check_expr_t (pn,ilist) tparams tenv e pt in
                (pn, eval env w)
            end
            bs
      in
      let boxArgs = List.map (fun (x, t) -> t) boxArgMap in
      with_context PushSubcontext $. fun () ->
      assert_pred (pn,ilist) h ghostenv boxArgMap inv real_unit $. fun h _ boxVarMap _ ->
      let boxIdTerm = get_unique_var_symb x BoxIdType in
      begin fun cont ->
        let rec iter handleChunks handleClauses =
          match handleClauses with
            (l, x, hpn, args)::handleClauses ->
            begin
            match try_assoc hpn hpmap with
              None -> static_error l "No such handle predicate"
            | Some (lhp, hpParamMap, hpInv, pbcs) ->
              let hpArgMap =
                match zip hpParamMap args with
                  None -> static_error l "Incorrect number of arguments."
                | Some bs ->
                  List.map
                    begin fun ((x, t), e) ->
                      let w = check_expr_t (pn,ilist) tparams tenv e t in
                      (x, eval env w)
                    end
                    bs
              in
              let handleIdTerm = (List.assoc x env) in
              let hpInvEnv = [("predicateHandle", handleIdTerm)] @ hpArgMap @ boxVarMap in
              with_context (Executing (h, hpInvEnv, expr_loc hpInv, "Checking handle predicate invariant")) $. fun () ->
              assert_term (eval hpInvEnv hpInv) h hpInvEnv (expr_loc hpInv) "Cannot prove handle predicate invariant.";
              let (_, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with 
			    None-> static_error l ("No such predicate family: "^hpn)
			  | Some x -> x
			  in
              iter (((hpn_symb, true), real_unit, handleIdTerm::boxIdTerm::List.map (fun (x, t) -> t) hpArgMap, None)::handleChunks) handleClauses
            end
          | [] -> cont handleChunks
        in
        iter [] handleClauses
      end $. fun handleChunks ->
      let (_, _, _, bcn_symb, _) = match try_assoc' (pn,ilist) bcn predfammap with
	    None -> static_error l ("No such predicate family: "^bcn)
	  | Some x-> x
	  in
      with_context PopSubcontext $. fun () ->
      tcont sizemap ((x, BoxIdType)::tenv) (x::ghostenv) (((bcn_symb, true), real_unit, boxIdTerm::boxArgs, None)::(handleChunks@h)) ((x, boxIdTerm)::env)
    | CreateHandleStmt (l, x, hpn, arg) ->
      if not pure then static_error l "Handle creation statements are allowed only in a pure context.";
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable.";
      let bcn =
        match chop_suffix hpn "_handle" with
          None -> static_error l "Handle creation statement must mention predicate name that ends in '_handle'."
        | Some bcn -> match try_assoc' (pn,ilist) bcn boxmap with
            None-> static_error l "No such box class."
          | Some bcn -> bcn
      in
      let w = check_expr_t (pn,ilist) tparams tenv arg BoxIdType in
      let boxIdTerm = ev w in
      let handleTerm = get_unique_var_symb x HandleIdType in
      let (_, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with
	    None -> static_error l ("No such predicate family: "^hpn)
	  | Some x-> x
	  in
      tcont sizemap ((x, HandleIdType)::tenv) (x::ghostenv) (((hpn_symb, true), real_unit, [handleTerm; boxIdTerm], None)::h) ((x, handleTerm)::env)
    | ReturnStmt (l, Some e) ->
      let tp = match try_assoc "#result" tenv with None -> static_error l "Void function cannot return a value: " | Some tp -> tp in
      let _ = if pure && not (List.mem "#result" ghostenv) then static_error l "Cannot return from a regular function in a pure context." in
      let w = check_expr_t (pn,ilist) tparams tenv e tp in
      return_cont h (Some (ev w))
    | ReturnStmt (l, None) -> return_cont h None
    | WhileStmt (l, e, p, ss, closeBraceLoc) ->
      let _ = if pure then static_error l "Loops are not yet supported in a pure context." in
      let e = check_expr_t (pn,ilist) tparams tenv e boolt in
      check_ghost ghostenv l e;
      let xs = block_assigned_variables ss in
      let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
      let (p, tenv') = check_pred (pn,ilist) tparams tenv p in
      assert_pred (pn,ilist) h ghostenv env p real_unit (fun h _ _ _ ->
        let bs = List.map (fun x -> (x, get_unique_var_symb x (List.assoc x tenv))) xs in
        let env = bs @ env in
        branch
          (fun _ ->
             assume_pred (pn,ilist) [] ghostenv env p real_unit None None (fun h' ghostenv' env' ->
               assume (eval_non_pure (pn,ilist) false h' env e) (fun _ ->
                 let lblenv =
                   List.map
                     begin fun (lbl, cont) ->
                       (lbl, fun blocks_done sizemap tenv ghostenv h'' env -> cont blocks_done sizemap tenv ghostenv (h'' @ h) env)
                     end
                     lblenv
                 in
                 verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv' ghostenv' h' env' ss (fun _ _ _ h'' env ->
                   let env = List.filter (fun (x, _) -> List.mem_assoc x tenv) env in
                   assert_pred (pn,ilist) h'' ghostenv env p real_unit (fun h''' _ _ _ ->
                     check_leaks h''' env closeBraceLoc "Loop leaks heap chunks."
                   )
                 ) (fun h'' retval -> return_cont (h'' @ h) retval)
               )
             )
          )
          (fun _ ->
             assume_pred (pn,ilist) h ghostenv env p real_unit None None (fun h ghostenv' env' ->
               assume (ctxt#mk_not (eval_non_pure (pn,ilist) false h env e)) (fun _ ->
                 tcont sizemap tenv' ghostenv' h env')))
      )
    | PerformActionStmt (lcb, nonpure_ctxt, pre_bcn, pre_bcp_pats, lch, pre_hpn, pre_hp_pats, lpa, an, aargs, atomic, ss, closeBraceLoc, post_bcp_args_opt, lph, post_hpn, post_hp_args) ->
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' (pn,ilist) pre_bcn boxmap with
          None -> static_error lcb "No such box class."
        | Some boxinfo -> boxinfo
      in
	  let pre_bcn=
	    match search' pre_bcn (pn,ilist) boxmap with
		  None-> static_error lcb "You cannot perform an action on a box class that has not yet been declared."
		| Some pre_bcn -> pre_bcn
	  in
      if not (List.mem pre_bcn boxes) then static_error lcb "You cannot perform an action on a box class that has not yet been declared.";
      let (pre_bcp_pats, tenv) = check_pats (pn,ilist) lcb tparams tenv (BoxIdType::List.map (fun (x, t) -> t) boxpmap) pre_bcp_pats in
      let (_, _, _, boxpred_symb, _) = match try_assoc' (pn,ilist) pre_bcn predfammap with 
	    Some x->x
	  | None -> static_error lcb ("Box predicate not found: "^pre_bcn)
	  in
      assert_chunk (pn,ilist) h ghostenv env lcb (boxpred_symb, true) real_unit DummyPat pre_bcp_pats (fun h box_coef ts chunk_size ghostenv env ->
        if not (atomic || box_coef == real_unit) then assert_false h env lcb "Box predicate coefficient must be 1 for non-atomic perform_action statement.";
        let (boxId::pre_boxPredArgs) = ts in
        let (pre_handlePred_parammap, pre_handlePred_inv) =
          if pre_hpn = pre_bcn ^ "_handle" then
            ([], True lch)
          else
            match try_assoc' (pn,ilist) pre_hpn hpmap with
              None -> static_error lch "No such handle predicate in box class."
            | Some (_, hppmap, inv, _) ->
              (hppmap, inv)
        in
        let (_, _, _, pre_handlepred_symb, _) = match try_assoc' (pn,ilist) pre_hpn predfammap with 
	      Some x->x
	    | None -> static_error lcb ("Box predicate not found: "^pre_bcn)
	    in
        let (pre_hp_pats, tenv) = check_pats (pn,ilist) lch tparams tenv (HandleIdType::List.map (fun (x, t) -> t) pre_handlePred_parammap) pre_hp_pats in
        let (pre_handleId_pat::pre_hpargs_pats) = pre_hp_pats in
        assert_chunk (pn,ilist) h ghostenv (("#boxId", boxId)::env) lch (pre_handlepred_symb, true) real_unit DummyPat (pre_handleId_pat::LitPat (Var (l, "#boxId", ref (Some LocalVar)))::pre_hpargs_pats)
          (fun h coef ts chunk_size ghostenv env ->
             if not (coef == real_unit) then assert_false h env lch "Handle predicate coefficient must be 1.";
             let (handleId::_::pre_handlePredArgs) = ts in
             let (apmap, pre, post) =
               match try_assoc an amap with
                 None -> static_error l "No such action in box class."
               | Some (_, apmap, pre, post) -> (apmap, pre, post)
             in
             let aargbs =
               match zip apmap aargs with
                 None -> static_error lpa "Incorrect number of action arguments."
               | Some bs ->
                 List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
             in
             let Some pre_boxargbs = zip boxpmap pre_boxPredArgs in
             let pre_boxArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_boxargbs in
             let Some pre_hpargbs = zip pre_handlePred_parammap pre_handlePredArgs in
             let pre_hpArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_hpargbs in
             with_context PushSubcontext $. fun () ->
             assume_pred (pn,ilist) h ghostenv pre_boxArgMap inv real_unit None None $. fun h _ pre_boxVarMap ->
             with_context PopSubcontext $. fun () ->
             assume (eval ([("predicateHandle", handleId)] @ pre_hpArgMap @ pre_boxVarMap) pre_handlePred_inv) (fun () ->
               let nonpureStmtCount = ref 0 in
               let ss =
                 List.map
                   begin function
                     NonpureStmt (l, _, s) when !nonpure_ctxt ->
                     nonpureStmtCount := !nonpureStmtCount + 1;
                     if atomic then
                     begin
                       let funcname =
                         match s with
                           CallStmt (lcall, g, targs, args, _) -> g
                         | Assign (lcall, x, CallExpr (_, g, _, _, _, _)) -> g
                         | DeclStmt (lcall, xtype, x, CallExpr (_, g, _, _, _, _)) -> g
                         | _ -> static_error l "A non-pure statement in the body of an atomic perform_action statement must be a function call."
                       in
                       match try_assoc funcname funcmap with
                         None -> static_error l "No such function."
                       | Some (l, k, tparams, rt, ps, atomic, pre, pre_tenv, post, body,fb,v) ->
                         if not atomic then static_error l "A non-pure statement in the body of an atomic perform_action statement must be a call of an atomic function."
                     end;
                     NonpureStmt (l, true, s)
                   | s -> s
                   end
                   ss
               in
               if atomic && !nonpureStmtCount <> 1 then static_error lpa "The body of an atomic perform_action statement must include exactly one non-pure statement.";
               verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env ->
                 with_context (Executing (h, env, closeBraceLoc, "Closing box")) $. fun () ->
                 with_context PushSubcontext $. fun () ->
                 let pre_env = [("actionHandle", handleId)] @ pre_boxVarMap @ aargbs in
                 assert_term (eval pre_env pre) h pre_env closeBraceLoc "Action precondition failure.";
                 let post_boxArgMap =
                   match post_bcp_args_opt with
                     None -> pre_boxArgMap
                   | Some (lpb, post_bcp_args) ->
                     begin
                       match zip boxpmap post_bcp_args with
                         None -> static_error lpb "Incorrect number of post-state box arguments."
                       | Some bs ->
                         List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                     end
                 in
                 assert_pred (pn,ilist) h ghostenv post_boxArgMap inv real_unit $. fun h _ post_boxVarMap _ ->
                 let old_boxVarMap = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxVarMap in
                 let post_env = [("actionHandle", handleId)] @ old_boxVarMap @ post_boxVarMap @ aargbs in
                 assert_term (eval post_env post) h post_env closeBraceLoc "Action postcondition failure.";
                 let (post_handlePred_parammap, post_handlePred_inv) =
                   if post_hpn = pre_bcn ^ "_handle" then
                     ([], True l)
                   else
                     match try_assoc post_hpn hpmap with
                       None -> static_error lph "Post-state handle predicate: No such handle predicate in box class."
                     | Some (_, hppmap, inv, _) ->
                       (hppmap, inv)
                 in
                 let (_, _, _, post_handlePred_symb, _) = match try_assoc' (pn,ilist) post_hpn predfammap with 
				   None-> static_error lph ("No such predicate family: "^post_hpn)
				 | Some x-> x
				 in
                 let post_hpargs =
                   match zip post_handlePred_parammap post_hp_args with
                     None -> static_error lph "Post-state handle predicate: Incorrect number of arguments."
                   | Some bs ->
                     List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                 in
                 let post_hpinv_env = [("predicateHandle", handleId)] @ post_hpargs @ post_boxVarMap in
                 with_context (Executing (h, post_hpinv_env, expr_loc post_handlePred_inv, "Checking post-state handle predicate invariant")) $. fun () ->
                 assert_term (eval post_hpinv_env post_handlePred_inv) h post_hpinv_env lph "Post-state handle predicate invariant failure.";
                 let boxChunk = ((boxpred_symb, true), box_coef, boxId::List.map (fun (x, t) -> t) post_boxArgMap, None) in
                 let hpChunk = ((post_handlePred_symb, true), real_unit, handleId::boxId::List.map (fun (x, t) -> t) post_hpargs, None) in
                 let h = boxChunk::hpChunk::h in
                 with_context PopSubcontext $. fun () ->
                 tcont sizemap tenv ghostenv h env
               ) return_cont
             )
          )
      )
    | BlockStmt (l, ss) ->
      let cont h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env -> cont h env) return_cont
    | PureStmt (l, s) ->
      begin
        match s with
          PerformActionStmt (_, nonpure_ctxt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) ->
          nonpure_ctxt := not pure
        | _ -> ()
      end;
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes true leminfo sizemap tenv ghostenv h env s tcont return_cont
    | GotoStmt (l, lbl) ->
      begin
        match try_assoc lbl lblenv with
          None -> static_error l "No such label."
        | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | LabelStmt (l, _) -> static_error l "Label statements cannot appear in this position."
    | InvariantStmt (l, _) -> static_error l "Invariant statements cannot appear in this position."
  and
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss cont return_cont =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss cont return_cont
        ) return_cont
      )
  and
    goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env return_cont block =
    let `Block (inv, ss, cont) = block in
    let l() =
      match (inv, ss) with
        (Some (l, _, _), _) -> l
      | (_, s::_) -> stmt_loc s
      | _ -> assert false (* A block that has no invariant and no body cannot be in a loop *)
    in
    begin
      match (List.memq block blocks_done, inv) with
        (true, _) when pure -> assert_false h env (l()) "Loops are not allowed in a pure context."
      | (true, None) -> assert_false h env (l()) "Loop invariant required."
      | (_, Some (l, inv, tenv)) ->
        assert_pred (pn,ilist) h ghostenv env inv real_unit (fun h _ _ _ ->
          check_leaks h env l "Loop leaks heap chunks."
        )
      | (false, None) ->
        let blocks_done = block::blocks_done in
        verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss (cont blocks_done) return_cont
    end
  and
    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss cont return_cont =
    let (decls, ss) =
      let rec iter decls ss =
        match ss with
          (DeclStmt _) as s::ss -> iter (s::decls) ss
        | _ -> (List.rev decls, ss)
      in
      iter [] ss
    in
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env decls cont return_cont
    end $. fun sizemap tenv ghostenv h env ->
    let assigned_vars = block_assigned_variables ss in
    let blocks =
      let rec iter blocks ss =
        if ss = [] then
          List.rev blocks
        else
          let (lbls, ss) =
            let rec iter2 lbls ss =
              match ss with
                LabelStmt (l, lbl)::ss ->
                iter2 ((l, lbl)::lbls) ss
              | _ -> (lbls, ss)
            in
            iter2 [] ss
          in
          let (inv, ss) =
            let some_inv l inv ss =
              let (inv, tenv) = check_pred (pn,ilist) tparams tenv inv in
              (Some (l, inv, tenv), ss)
            in
            match ss with
              (PureStmt (_, InvariantStmt (l, inv)))::ss -> some_inv l inv ss
            | InvariantStmt (l, inv)::ss ->
              if not pure then static_error l "Invariant statements must be inside an annotation.";
              some_inv l inv ss
            | _ -> (None, ss)
          in
          let (body, ss) =
            let rec iter2 body ss =
              match ss with
                [] | LabelStmt _::_ | InvariantStmt _::_ | PureStmt (_, InvariantStmt _)::_ -> (List.rev body, ss)
              | s::ss -> iter2 (s::body) ss
            in
            iter2 [] ss
          in
          iter ((lbls, inv, body)::blocks) ss
      in
      iter [] ss
    in
    let lblenv_ref = ref [] in
    let (lblenv, blocks) =
      let rec iter blocks =
        match blocks with
          [] -> (lblenv, [])
        | (lbls, inv, ss)::blocks ->
          let (lblenv, blocks') = iter blocks in
          let cont blocks_done sizemap tenv ghostenv h env =
            match blocks' with
              [] -> cont sizemap tenv ghostenv h env
            | block'::_ -> goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo sizemap tenv ghostenv h env return_cont block'
          in
          let block' = `Block (inv, ss, cont) in
          let lblenv =
            let cont blocks_done sizemap tenv ghostenv h env =
              goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo sizemap tenv ghostenv h env return_cont block'
            in
            let rec iter lblenv lbls =
              match lbls with
                [] -> lblenv
              | (l, lbl)::lbls ->
                if List.mem_assoc lbl lblenv then static_error l "Duplicate label";
                iter ((lbl, cont)::lblenv) lbls
            in
            iter lblenv lbls
          in
          (lblenv, block'::blocks')
      in
      iter blocks
    in
    lblenv_ref := lblenv;
    begin
      match blocks with
        [] -> cont sizemap tenv ghostenv h env
      | block0::_ -> goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env return_cont block0
    end;
    begin
      List.iter
        begin fun (`Block (inv, ss, cont) as block) ->
          match inv with
            None -> ()
          | Some (l, inv, tenv) ->
            let env =
              flatmap
                begin fun (x, v) ->
                  match try_assoc x tenv with
                    None -> []
                  | Some t ->
                    if List.mem x assigned_vars then
                      [(x, get_unique_var_symb x t)]
                    else
                      [(x, v)]
                end
                env
            in
            assume_pred (pn,ilist) [] ghostenv env inv real_unit None None (fun h ghostenv env ->
              let blocks_done = block::blocks_done in
              verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo sizemap tenv ghostenv h env ss (cont blocks_done) return_cont
            )
        end
        blocks
    end
  in
  
  let params xmap=
    List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap
  in
  
  let switch_stmt ss env=
    match ss with
      [SwitchStmt (_, Var (_, x, _), _)] ->
        (match try_assoc x env with
           None -> ([], None)
         | Some t -> ([(t, 0)], Some x)
        )
    | _ -> ([], None)
  in
  
  let get_fields (pn,ilist) cn lm=
    match try_assoc' (pn,ilist) cn classmap with
      Some (_,_,fds_opt,_,_,_,_,_)-> (match fds_opt with Some fds -> fds | None -> [])
    | None -> static_error lm ("No class was found: "^cn)
  in
  
  let _ =
    let rec verify_cons (pn,ilist) cn boxes lems cons=
      match cons with
     [] -> ()
      | (xmap, (lm,pre,post,ss,v))::rest ->
          match ss with
            None -> let (((_,p),_,_),((_,_),_,_))=lm in 
              if Filename.check_suffix p ".javaspec" then verify_cons (pn,ilist) cn boxes lems rest
              else static_error lm "Constructor specification is only allowed in javaspec files!"
          | Some ss ->
              let _ = push() in
              let env = params xmap in
              let (sizemap, indinfo) = switch_stmt ss env in
              let (in_pure_context, leminfo, lems', ghostenv) = (false, None, lems, []) in
              let (_, tenv) = check_pred (pn,ilist) [] (("this", ObjType(cn))::xmap) pre in
              let _ =
                assume_pred (pn,ilist) [] ghostenv env pre real_unit (Some 0) None
                (fun h ghostenv env ->
                  let do_body h ghostenv env=
                    let do_return h env_post = assert_pred (pn,ilist) h ghostenv env_post post real_unit 
                    (fun h ghostenv env size_first ->(check_leaks h env lm "Function leaks heap chunks."))
                    in
                    let return_cont h retval =
                      match retval with None -> do_return h env | Some t -> do_return h (("this", t)::env)
                    in
                    verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo sizemap tenv ghostenv h env ss 
                    (fun _ _ _ h _ -> return_cont h None ) return_cont
                  in
                  let result = get_unique_var_symb "result" (ObjType cn) in
                  let this = get_unique_var_symb "this" (ObjType cn) in
                  assume_neq this (ctxt#mk_intlit 0) 
                      (fun()->( assume_eq result this 
                        (fun()->
                          let fds= get_fields (pn,ilist) cn lm in 
                          let rec iter h fds =
                            match fds with
                             [] -> 
                               let env'= update env "result" result in
                               let env''= update env' "this" this in
                               let (_, (_, _, _, malloc_block_symb, _)) = (List.assoc cn malloc_block_pred_map) in
                               (do_body (h @ [((malloc_block_symb, true), real_unit, [result], None)]) ghostenv env'')
                           | (f, (lf, t,vis))::fds ->
                               let fref = new fieldref f in
                               fref#set_parent cn; fref#set_range t; assume_field h fref result (get_unique_var_symb "value" t) real_unit (fun h -> iter h fds)
                          in
                          iter h fds
                        )
                       )
                      )
                )
              in
              let _ = pop() in
              verify_cons (pn,ilist) cn boxes lems' rest
    in
    let rec verify_meths (pn,ilist) boxes lems meths=
      match meths with
        [] -> ()
      | (g, (l,rt, ps,pre,post,sts,fb,v))::meths ->
        match sts with
          None -> let (((_,p),_,_),((_,_),_,_))=l in 
            if Filename.check_suffix p ".javaspec" then verify_meths (pn,ilist) boxes lems meths
            else static_error l "Constructor specification is only allowed in javaspec files!"
        | Some sts ->(
            let ss= if fb=Instance then CallStmt (l, "assume_class_this", [], [],Instance)::sts else sts in
            let _ = push() in
            let env = params ps in (* actual params invullen *)
            let (sizemap, indinfo) = switch_stmt ss env in
            let tenv = match rt with None ->ps | Some rt -> ("#result", rt)::ps in
            let (in_pure_context, leminfo, lems', ghostenv) =(false, None, lems, []) in
            let (_, tenv) = check_pred (pn,ilist) [] tenv pre in
            let _ =
              assume_pred (pn,ilist) [] ghostenv env pre real_unit (Some 0) None (fun h ghostenv env ->
              let do_return h env_post = assert_pred (pn,ilist) h ghostenv env_post post real_unit (fun h ghostenv env size_first ->(check_leaks h env l "Function leaks heap chunks."))
              in
              let return_cont h retval =
                match (rt, retval) with
                  (None, None) -> do_return h env
                | (Some tp, Some t) -> do_return h (("result", t)::env)
                | (None, Some _) -> assert_false h env l "Void function returns a value."
                | (Some _, None) -> assert_false h env l "Non-void function does not return a value."
              in
              verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo sizemap tenv ghostenv h env ss (fun _ _ _ h _ -> return_cont h None) return_cont
              )
            in
            let _ = pop() in
            verify_meths (pn,ilist) boxes lems' meths
            )
    in
    let rec verify_classes boxes lems classm=
      match classm with
        [] -> ()
      | (cn,(l,meths,_,cons,_,_,pn,ilist))::classm ->
          let _=
            match cons with
              None -> ()
            | Some cons -> verify_cons (pn,ilist) cn boxes lems cons
          in
          (match meths with
            None -> verify_classes boxes lems classm
          | Some m -> verify_meths (pn,ilist) boxes lems m; verify_classes  boxes lems classm)
    in
  let rec verify_funcs (pn,ilist)  boxes lems ds =
    match ds with
     [] -> (match file_type path with
              Java -> verify_classes boxes lems classmap;
            | _ -> () 
            )
    | Func (l, Lemma, _, rt, g, ps, _, _, _, None, _, _)::ds -> let g=full_name pn g in
      verify_funcs (pn,ilist)  boxes (g::lems) ds
    | Func (_, k, _, _, g, _, _, functype_opt, _, Some _, _, _)::ds when k <> Fixpoint -> let g=full_name pn g in
      let (l, k, tparams, rt, ps, atomic, pre, pre_tenv, post, Some (Some (ss, closeBraceLoc)),fb,v) = (List.assoc g funcmap)in
      let _ = push() in
      let env = params ps in (* actual params invullen *)
      let (sizemap, indinfo) =
        match ss with
          [SwitchStmt (_, Var (_, x, _), _)] -> (
          match try_assoc x env with
            None -> ([], None)
          | Some t -> ([(t, 0)], Some x)
          )
        | _ -> ([], None)
      in
      let (tenv, rxs) =
        match rt with
          None -> (pre_tenv, [])
        | Some rt -> (("#result", rt)::pre_tenv, ["#result"])
      in
      let (in_pure_context, leminfo, lems', ghostenv) =
        if k = Lemma then 
          (true, Some (lems, g, indinfo), g::lems, List.map (function (p, t) -> p) ps @ rxs)
        else
          (false, None, lems, [])
      in
      let _ =
        check_should_fail () $. fun _ ->
        assume_pred (pn,ilist) [] ghostenv env pre real_unit (Some 0) None (fun h ghostenv env ->
          let do_return h env_post =
            match file_type path with
            Java ->assert_pred (pn,ilist) h ghostenv env_post post real_unit (fun h ghostenv env size_first ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            )
            |_ ->
             assert_pred (pn,ilist) h ghostenv env_post post real_unit (fun h ghostenv env size_first ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            )
          in
          let return_cont h retval =
            match (rt, retval) with
              (None, None) -> do_return h env
            | (Some tp, Some t) -> do_return h (("result", t)::env)
            | (None, Some _) -> assert_false h env l "Void function returns a value."
            | (Some _, None) -> assert_false h env l "Non-void function does not return a value."
          in
          verify_block (pn,ilist) [] [] tparams boxes in_pure_context leminfo sizemap tenv ghostenv h env ss (fun _ _ _ h _ -> return_cont h None) return_cont
        )
      in
      let _ = pop() in
      begin
        match functype_opt with
          Some ftn ->
          assume_is_functype g ftn (* Contract implication was already checked during construction of funcmap *)
        | _ -> ()
      end;
      verify_funcs (pn,ilist)  boxes lems' ds
    | BoxClassDecl (l, bcn, _, _, _, _)::ds -> let bcn=full_name pn bcn in
      let (l, boxpmap, boxinv, boxvarmap, amap, hpmap) = match try_assoc' (pn,ilist) bcn boxmap with 
	    None -> static_error l ("Box class wasn't found: "^bcn)
	  | Some x -> x
	  in
      let old_boxvarmap = List.map (fun (x, t) -> ("old_" ^ x, t)) boxvarmap in
      let leminfo = Some (lems, "", None) in
      List.iter
        (fun (hpn, (l, pmap, inv, pbcs)) ->
           let pbcans =
             List.map
               (fun (PreservedByClause (l, an, xs, ss)) ->
                  begin
                  match try_assoc an amap with
                    None -> static_error l "No such action."
                  | Some (_, apmap, pre, post) ->
                    let _ =
                      let rec iter ys xs =
                        match xs with
                          [] -> ()
                        | x::xs ->
                          if List.mem_assoc x boxvarmap then static_error l "Action parameter name clashes with box variable.";
                          if List.mem_assoc x pmap then static_error l "Action parameter name clashes with handle predicate parameter.";
                          if List.mem x ys then static_error l "Duplicate action parameter.";
                          if startswith x "old_" then static_error l "Action parameter name cannot start with old_.";
                          iter (x::ys) xs
                      in
                      iter [] xs
                    in
                    let apbs =
                      match zip xs apmap with
                        None -> static_error l "Incorrect number of action parameters."
                      | Some bs -> bs
                    in
                    let apmap' = List.map (fun (x, (_, t)) -> (x, t)) apbs in
                    let tenv = boxvarmap @ old_boxvarmap @ pmap @ apmap' in
                    push();
                    let actionHandle = get_unique_var_symb "actionHandle" HandleIdType in
                    let predicateHandle = get_unique_var_symb "predicateHandle" HandleIdType in
                    assume (ctxt#mk_not (ctxt#mk_eq actionHandle predicateHandle)) (fun () ->
                    let pre_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb ("old_" ^ x) t)) boxpmap in
                    with_context (Executing ([], [], l, "Checking preserved_by clause.")) $. fun () ->
                    with_context PushSubcontext $. fun () ->
                    assume_pred (pn,ilist) [] [] pre_boxargs boxinv real_unit None None $. fun _ _ pre_boxvars ->
                    let old_boxvars = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxvars in
                    let post_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) boxpmap in
                    assume_pred (pn,ilist) [] [] post_boxargs boxinv real_unit None None $. fun _ _ post_boxvars ->
                    with_context PopSubcontext $. fun () ->
                    let hpargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) pmap in
                    let aargs = List.map (fun (x, (y, t)) -> (x, y, get_unique_var_symb x t)) apbs in
                    let apre_env = List.map (fun (x, y, t) -> (y, t)) aargs in
                    let ghostenv = List.map (fun (x, t) -> x) tenv in
                    assume (eval (pn,ilist) None ([("actionHandle", actionHandle)] @ pre_boxvars @ apre_env) pre) (fun () ->
                      assume (eval (pn,ilist) None ([("predicateHandle", predicateHandle)] @ pre_boxvars @ hpargs) inv) (fun () ->
                        assume (eval (pn,ilist) None ([("actionHandle", actionHandle)] @ post_boxvars @ old_boxvars @ apre_env) post) (fun () ->
                          let aarg_env = List.map (fun (x, y, t) -> (x, t)) aargs in
                          let env = [("actionHandle", actionHandle)] @ [("predicateHandle", predicateHandle)] @
                            post_boxvars @ old_boxvars @ aarg_env @ hpargs in
                          verify_cont (pn,ilist) [] [] [] boxes true leminfo [] tenv ghostenv [] env ss (fun _ _ _ _ _ ->
                            let post_inv_env = [("predicateHandle", predicateHandle)] @ post_boxvars @ hpargs in
                            assert_term (eval (pn,ilist) None post_inv_env inv) [] post_inv_env l "Handle predicate invariant preservation check failure."
                          ) (fun _ _ -> static_error l "Return statements are not allowed in handle predicate preservation proofs.")
                        )
                      )
                    )
                    );
                    pop();
                    an
                  end)
               pbcs
           in
           List.iter (fun (an, _) -> if not (List.mem an pbcans) then static_error l ("No preserved_by clause for action '" ^ an ^ "'.")) amap)
        hpmap;
      verify_funcs (pn,ilist)  (bcn::boxes) lems ds
    | _::ds -> verify_funcs (pn,ilist)  boxes lems ds
  in
  let lems0 = flatmap (function (g, (l, Lemma, tparams, rt, ps, atomic, pre, pre_tenv, post, body, fb, v)) -> [g] | _ -> []) funcmap0 in
  let rec verify_funcs' boxes lems ps=
    match ps with
      PackageDecl(l,pn,il,ds)::rest-> verify_funcs (pn,il)  boxes lems ds;verify_funcs' boxes lems rest
    | [] -> ()
  in
  verify_funcs' [] lems0 ps
  
  in
  
  (structmap1, inductivemap1, purefuncmap1,predctormap1, fixpointmap1, malloc_block_pred_map1, field_pred_map1, predfammap1, predinstmap1, functypemap1, funcmap1, !prototypes_used, prototypes_implemented,boxmap,classmap1,interfmap1)
  
  in
  
  let main_file= ref ("",dummy_loc) in
  let jardeps= ref [] in
  let basepath=(Filename.basename path) in
  let dirpath= (Filename.dirname path) in
  let (prototypes_used, prototypes_implemented) =
    let (headers, ds)=
      match file_type basepath with
      Java->if Filename.check_suffix path ".jarsrc" then
              let (main,impllist,jarlist,jdeps)=parse_jarsrc_file dirpath basepath reportRange in
              let ds= (List.map(fun x->parse_java_file(Filename.concat dirpath x)reportRange)impllist)in
              let specpath= (Filename.chop_extension basepath)^".jarspec" in
              main_file:=main;
              jardeps:=jdeps;
              if Sys.file_exists (Filename.concat dirpath specpath) then
                (jarlist@[(dummy_loc,specpath)],ds)
              else
                ([],ds)
            else
              ([],[parse_java_file path reportRange])
      | _-> 
        parse_c_file path reportRange reportShouldFail
    in
    let result =
      check_should_fail ([], []) $. fun () ->
      let (_, _, _, _, _, _, _,_,_, _, _, prototypes_used, prototypes_implemented,_,_,_) = check_file true programDir headers ds in
      (prototypes_used, prototypes_implemented)
    in
    begin
      match !shouldFailLocs with
        [] -> ()
      | l::_ -> static_error l "No error found on line."
    end;
    result
  in

  let _=
    let rec iter (file,l) mainlist=
      match mainlist with
        [] -> static_error l "no main method was found"
      | (cn,l)::_ when cn=file -> ()
      | _::rest -> iter (file,l) rest
    in
    if !main_file<>("",dummy_loc) then
    iter !main_file !main_meth
  in
  
  
  let create_jardeps_file() =
    let jardeps_filename = Filename.chop_extension path ^ ".jardeps" in
    if emit_manifest then
      let file = open_out jardeps_filename in
      do_finally (fun () ->
        List.iter (fun line -> output_string file (line ^ "\n")) !jardeps
      ) (fun () -> close_out file)
    else
      jardeps_map := (jardeps_filename, !jardeps)::!jardeps_map
  in
  
  let create_manifest_file() =
    let manifest_filename = Filename.chop_extension path ^ ".vfmanifest" in
    let sorted_lines protos =
      let lines = List.map (fun (g, (((_, path), _, _), _)) -> path ^ "#" ^ g) protos in
      List.sort compare lines
    in
    let lines =
      List.map (fun line -> ".requires " ^ line) (sorted_lines prototypes_used)
      @
      List.map (fun line -> ".provides " ^ line) (sorted_lines prototypes_implemented)
    in
    if emit_manifest then
      let file = open_out manifest_filename in
      do_finally (fun () ->
        List.iter (fun line -> output_string file (line ^ "\n")) lines
      ) (fun () -> close_out file)
    else
      manifest_map := (manifest_filename, lines)::!manifest_map
  in
  if file_type path <>Java then
  create_manifest_file()
  else
    if Filename.check_suffix path ".jarsrc" then create_jardeps_file()

let verify_program_with_stats ctxt print_stats verbose path reportRange breakpoint =
  do_finally
    (fun () -> verify_program_core ctxt verbose path reportRange breakpoint)
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
      
let verify_program prover print_stats options path reportRange breakpoint =
  lookup_prover prover
    (object
       method run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit =
         fun ctxt -> verify_program_with_stats ctxt print_stats options path reportRange breakpoint
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
        if List.mem_assoc manifest_path !manifest_map then
          List.assoc manifest_path !manifest_map
        else if Sys.file_exists manifest_path then
          let file = open_in manifest_path in
          do_finally (fun () ->
            let rec iter () =
              try
                let line = input_line file in
                let n = String.length line in
                let line = if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line in
                line::iter()
              with
                End_of_file -> []
            in
            iter()
          ) (fun () -> close_in file)
        else failwith ("VeriFast link phase error: could not find .vfmanifest file '" ^ manifest_path ^ "' for module '" ^ modulepath ^ "'. Re-verify the module using the -emit_manifest option.")
      in
      let rec iter0 impls' lines =
        match lines with
          [] -> iter impls' modulepaths
        | line::lines ->
          let space = String.index line ' ' in
          let command = String.sub line 0 space in
          let symbol = String.sub line (space + 1) (String.length line - space - 1) in
          let n = String.length symbol in
          for i = 0 to n - 1 do if symbol.[i] = '/' then symbol.[i] <- '\\' done;
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
