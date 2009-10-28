open Proverapi
open Big_int
open Printf
open Num

(* You can get an outline of this file in Notepad++ by copying the text
 * "Region:" to the clipboard and choosing
 * TextFX->Viz->Hide Lines without (clipboard) text
 * Get all lines back by choosing
 * TextFX->Viz->Show Between-Selected or All-Reset Lines
 *)

(* Region: General-purpose utility functions *)

let num_of_ints p q = div_num (num_of_int p) (num_of_int q)

let fprintff format = kfprintf (fun chan -> flush chan) format
let printff format = fprintff stdout format

(** Keeps manifests produced by the compilation phase, for use during the linking phase. Avoids writing manifest files to disk. *)
let manifest_map: (string * string list) list ref = ref []
let jardeps_map: (string * string list) list ref = ref []

(** Facilitates continuation-passing-style programming. *)
let ($.) f x = f x

(** Same as [List.for_all2 f (take n xs) (take n ys)] *)
let for_all_take2 f n xs ys =
  let rec iter n xs ys =
    if n <= 0 then true else
    match (xs, ys) with
      (x::xs, y::ys) -> f x y && iter (n - 1) xs ys
  in
  iter n xs ys

let intersect xs ys = List.filter (fun x -> List.mem x ys) xs
let flatmap f xs = List.concat (List.map f xs)
let rec drop n xs = if n = 0 then xs else drop (n - 1) (List.tl xs)
let rec take n xs = if n = 0 then [] else match xs with x::xs -> x::take (n - 1) xs
(* Same as [(take n xs, drop n xs)] *)
let take_drop n xs =
  let rec iter left right k =
    if k = 0 then
      (List.rev left, right)
    else
      match right with
        [] -> (List.rev left, right)
      | x::right -> iter (x::left) right (k - 1)
  in
  iter [] xs n

let rec list_make n x = if n = 0 then [] else x::list_make (n - 1) x

let remove f xs = List.filter (fun x -> not (f x)) xs

let rec distinct xs =
  match xs with
    [] -> true
  | x::xs -> not (List.mem x xs) && distinct xs
  
let rec index_of x xs i =
  match xs with
    [] -> None
  | y :: ys when x = y -> Some(i)
  | _ :: ys -> index_of x ys (i + 1)

(** Same as [List.assoc x xys], except returns [Some y] if [xys] binds [x] to [y], or [None] if [xys] does not contain a binding for [x]. *)
let rec try_assoc x xys =
  match xys with
    [] -> None
  | (x', y)::xys when x' = x -> Some y
  | _::xys -> try_assoc x xys
  
let rec try_assoc0 x xys =
  match xys with
    [] -> None
  | ((x', y) as xy)::xys when x' = x -> Some xy
  | _::xys -> try_assoc0 x xys

(** Same as [try_assoc], except performs reference comparison instead of structural comparison. *)
let rec try_assq x xys =
  match xys with
    [] -> None
  | (x', y)::xys when x' == x -> Some y
  | _::xys -> try_assq x xys

(** Same as [try_assoc], except also returns the index of the binding. *)
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

(** Same as [try_assoc x (xys1 @ xys2)] *)
let try_assoc2 x xys1 xys2 =
  match try_assoc x xys1 with
    None -> try_assoc x xys2
  | result -> result

let assoc2 x xys1 xys2 =
  let (Some y) = try_assoc2 x xys1 xys2 in y

exception IsNone

let get x = 
  match x with
    None -> raise IsNone
  | Some x -> x

let bindir = Filename.dirname Sys.executable_name
let rtdir = Filename.concat bindir "rt"

(* Region: Statistics *)

class stats =
  object (self)
    val mutable stmtsParsedCount = 0
    val mutable stmtExecCount = 0
    val mutable execStepCount = 0
    val mutable branchCount = 0
    val mutable proverAssumeCount = 0
    val mutable definitelyEqualSameTermCount = 0
    val mutable definitelyEqualQueryCount = 0
    val mutable proverOtherQueryCount = 0
    val mutable proverStats = ""
    
    method stmtParsed = stmtsParsedCount <- stmtsParsedCount + 1
    method stmtExec = stmtExecCount <- stmtExecCount + 1
    method execStep = execStepCount <- execStepCount + 1
    method branch = branchCount <- branchCount + 1
    method proverAssume = proverAssumeCount <- proverAssumeCount + 1
    method definitelyEqualSameTerm = definitelyEqualSameTermCount <- definitelyEqualSameTermCount + 1
    method definitelyEqualQuery = definitelyEqualQueryCount <- definitelyEqualQueryCount + 1
    method proverOtherQuery = proverOtherQueryCount <- proverOtherQueryCount + 1
    method appendProverStats s = proverStats <- proverStats ^ s
    
    method printStats =
      print_endline ("Statements parsed: " ^ string_of_int stmtsParsedCount);
      print_endline ("Statement executions: " ^ string_of_int stmtExecCount);
      print_endline ("Execution steps (including assertion production/consumption steps): " ^ string_of_int execStepCount);
      print_endline ("Symbolic execution forks: " ^ string_of_int branchCount);
      print_endline ("Prover assumes: " ^ string_of_int proverAssumeCount);
      print_endline ("Term equality tests -- same term: " ^ string_of_int definitelyEqualSameTermCount);
      print_endline ("Term equality tests -- prover query: " ^ string_of_int definitelyEqualQueryCount);
      print_endline ("Term equality tests -- total: " ^ string_of_int (definitelyEqualSameTermCount + definitelyEqualQueryCount));
      print_endline ("Other prover queries: " ^ string_of_int proverOtherQueryCount);
      print_endline ("Prover statistics:\n" ^ proverStats)
  end

let stats = new stats

(* Region: lexical analysis *)

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
  | CharToken of char
  | PreprocessorSymbol of string
  | Eol
  | ErrorToken

(** Base path, relative path, line (1-based), column (1-based) *)
type srcpos = ((string * string) * int * int)
(** A range of source code: start position, end position *)
type loc = (srcpos * srcpos)

exception ParseException of loc * string

(** Like the Stream module of the O'Caml library, except that it supports a limited form of backtracking using [push].
    Used implicitly by the parser. *)
module Stream = struct
  exception Failure
  exception Error of string
  type 'a t = (int -> 'a option) * (int ref) * ('a option list ref)
  let from f = (f, ref 0, ref [])
  let peek (f, counter, buffer) =
    match !buffer with
      tok::_ -> tok
    | [] ->
      let tok = f !counter in
      incr counter;
      buffer := [tok];
      tok
  let junk (f, counter, buffer) =
    buffer := List.tl !buffer
  let push tok (f, counter, buffer) =
    buffer := tok::!buffer
  let empty stream = if peek stream = None then () else raise Failure
  let npeek n ((f, counter, buffer): 'a t): 'a list =
    let rec iter n buffer =
      if n = 0 then [] else
      match buffer with
        [None] -> []
      | tok::toks -> tok::iter (n - 1) toks
      | [] ->
        let tok = f !counter in
        incr counter;
        if tok = None then [None] else tok::iter (n - 1) []
    in
    buffer := iter n !buffer;
    List.flatten (List.map (function None -> [] | Some tok -> [tok]) !buffer)
  let iter (g: 'a -> unit) (stream: 'a t): unit =
    let rec iter () =
      match peek stream with
        None -> ()
      | Some tok ->
        g tok;
        junk stream;
        iter ()
    in
    iter ()
end

(* The lexer *)

let big_int_of_hex_string s =
  let rec iter k weight sum =
    if k < 2 then
      sum
    else
      let c = int_of_char (s.[k]) in
      let digit =
        if int_of_char '0' <= c && c <= int_of_char '9' then
          c - int_of_char '0'
        else
          c - int_of_char 'A' + 10
      in
      iter (k - 1) (mult_int_big_int 16 weight) (add_big_int sum (mult_int_big_int digit weight))
  in
  iter (String.length s - 1) unit_big_int zero_big_int

(** For syntax highlighting. *)
type range_kind =
    KeywordRange
  | GhostKeywordRange
  | GhostRange
  | GhostRangeDelimiter
  | CommentRange
  | ErrorRange

(** The lexer.
    @param reportShouldFail Function that will be called whenever a should-fail directive is found in the source code.
      Should-fail directives are of the form //~ and are used for writing negative VeriFast test inputs. See tests/errors.
  *)
let make_lexer_core keywords ghostKeywords path text reportRange inComment inGhostRange exceptionOnError reportShouldFail =
  let textlength = String.length text in
  let textpos = ref 0 in
  let text_peek () = if !textpos = textlength then '\000' else text.[!textpos] in
  let text_junk () = incr textpos in
  
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

  let current_srcpos() = (path, !line, !textpos - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in

  let in_single_line_annotation = ref false in
  
  let ghost_range_start: srcpos option ref = ref (if inGhostRange then Some (current_srcpos()) else None) in
  
  let ignore_eol = ref true in
  
  let error msg =
      raise (Stream.Error msg)
  in
  
  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  let ghost_kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add ghost_kwd_table s (Kwd s)) (keywords @ ghostKeywords);
  let get_kwd_table() = if !ghost_range_start = None then kwd_table else ghost_kwd_table in
  let ident_or_keyword id isAlpha =
    try
      let t = Hashtbl.find (get_kwd_table()) id in
      if isAlpha then
        reportRange (if !ghost_range_start = None then KeywordRange else GhostKeywordRange) (current_loc());
      t
    with
      Not_found ->
      let n = String.length id in
      if n > 2 && id.[n - 2] = '_' && id.[n - 1] = 'H' then PreprocessorSymbol id else Ident id
  and keyword_or_error c =
    let s = String.make 1 c in
    try Hashtbl.find (get_kwd_table()) s with
      Not_found -> error "Illegal character"
  in
  let start_token() =
    tokenpos := !textpos;
    token_srcpos := current_srcpos()
  in
  let new_loc_line () =
      line := !line + 1;
      linepos := !textpos
  in
  let rec next_token () =
    if !in_comment then
    begin
      in_comment := false;
      multiline_comment ()
    end
    else
    let new_line () =
      new_loc_line ();
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        ghost_range_end();
        Some (Kwd "@*/")
      ) else if !ignore_eol then
        next_token ()
      else
        Some Eol
    in
    match text_peek () with
      (' ' | '\009' | '\026' | '\012') ->
        text_junk (); next_token ()
    | '\010' ->
        text_junk (); new_line ()
    | '\013' ->
        text_junk ();
        if text_peek () = '\010' then text_junk ();
        new_line ()
    |('A'..'Z' | 'a'..'z' | '_' | '\128'..'\255' as c) ->
        start_token();
        text_junk ();
        ident ()
    | '(' -> text_junk (); Some(ident_or_keyword "(" false)
    | ('!' | '%' | '&' | '$' | '#' | '+' | ':' | '<' | '=' | '>' |
       '?' | '@' | '\\' | '~' | '^' | '|' as c) ->
        start_token();
        text_junk ();
        reset_buffer (); store c; ident2 ()
    | ('0'..'9' as c) ->
        start_token();
        text_junk ();
        reset_buffer (); store c; number ()
    | '\'' ->
        start_token();
        text_junk ();
        let c =
          try char () with
            Stream.Failure -> error "Bad character literal."
        in
        begin match text_peek () with
          '\'' -> text_junk (); Some (CharToken c)
        | _ -> error "Single quote expected."
        end
    | '"' ->
        start_token();
        text_junk ();
        reset_buffer (); Some (String (string ()))
    | '-' -> start_token(); text_junk (); neg_number ()
    | '/' -> start_token(); text_junk (); maybe_comment ()
    | '\000' ->
      in_ghost_range := !ghost_range_start <> None;
      ghost_range_end();
      None
    | c -> start_token(); text_junk (); Some (keyword_or_error c)
  and ident () =
    match text_peek () with
      ('A'..'Z' | 'a'..'z' | '\128'..'\255' | '0'..'9' | '_' | '\'' as c) ->
      text_junk (); ident ()
    | _ -> Some (ident_or_keyword (String.sub text !tokenpos (!textpos - !tokenpos)) true)
  and ident2 () =
    match text_peek () with
      ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' |
       '>' | '?' | '@' | '\\' | '~' | '^' | '|' | '*' as c) ->
        text_junk (); store c; ident2 ()
    | _ ->
      let s = get_string() in
      if s = "@*/" then
      begin
        ghost_range_end();
        reportRange GhostRangeDelimiter (current_loc());
        Some (Kwd "@*/")
      end
      else
        Some (ident_or_keyword s false)
  and neg_number () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk ();
        reset_buffer (); store '-'; store c; number ()
    | _ -> reset_buffer (); store '-'; ident2 ()
  and number () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; number ()
    | 'x' -> text_junk (); store 'x'; hex_number ()
    | '.' ->
        text_junk (); store '.'; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | _ -> Some (Int (big_int_of_string (get_string ())))
  and hex_number () =
    match text_peek () with
      ('0'..'9' | 'A'..'F') as c -> text_junk (); store c; hex_number ()
    | _ -> Some (Int (big_int_of_hex_string (get_string ())))
  and decimal_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | _ -> Some (Float (float_of_string (get_string ())))
  and exponent_part () =
    match text_peek () with
      ('+' | '-' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> end_exponent_part ()
  and end_exponent_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> Some (Float (float_of_string (get_string ())))
  and string () =
    match text_peek () with
      '"' -> text_junk (); get_string ()
    | '\\' ->
        text_junk ();
        let c =
          try escape () with
            Stream.Failure -> error "Bad string literal."
        in
        store c; string ()
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); store c; string ()
    | _ -> raise Stream.Failure
  and char () =
    match text_peek () with
      '\\' ->
        text_junk ();
        begin try escape () with
          Stream.Failure -> error "Bad character literal."
        end
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); c
    | _ -> raise Stream.Failure
  and escape () =
    match text_peek () with
      'n' -> text_junk (); '\n'
    | 'r' -> text_junk (); '\r'
    | 't' -> text_junk (); '\t'
    | ('0'..'9' as c1) ->
        text_junk ();
        begin match text_peek () with
          ('0'..'9' as c2) ->
            text_junk ();
            begin match text_peek () with
              ('0'..'9' as c3) ->
                text_junk ();
                Char.chr
                  ((Char.code c1 - 48) * 100 + (Char.code c2 - 48) * 10 +
                     (Char.code c3 - 48))
            | _ -> Char.chr ((Char.code c1 - 48) * 10 + (Char.code c2 - 48))
            end
        | _ -> Char.chr (Char.code c1 - 48)
        end
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); c
    | _ -> raise Stream.Failure
  and ghost_range_end_at srcpos =
    match !ghost_range_start with
      None -> ()
    | Some sp -> reportRange GhostRange (sp, srcpos); ghost_range_start := None
  and ghost_range_end () = ghost_range_end_at (current_srcpos())
  and maybe_comment () =
    match text_peek () with
      '/' ->
      text_junk ();
      (
        match text_peek () with
          '@' ->
          begin
            text_junk ();
            if !ghost_range_start <> None then raise Stream.Failure;
            in_single_line_annotation := true;
            ghost_range_start := Some !token_srcpos;
            reportRange GhostRangeDelimiter (current_loc());
            Some (Kwd "/*@")
          end
        | _ ->
          if !in_single_line_annotation then (
            in_single_line_annotation := false;
            ghost_range_end_at (path, !line, !textpos - 2 - !linepos + 1);
            single_line_comment ();
            Some (Kwd "@*/")
          ) else (
            single_line_comment (); next_token ()
          )
      )
    | '*' ->
      text_junk ();
      (
        match text_peek () with
          '@' ->
          text_junk ();
          if !ghost_range_start <> None then raise Stream.Failure;
          ghost_range_start := Some !token_srcpos;
          reportRange GhostRangeDelimiter (current_loc());
          Some (Kwd "/*@")
        | _ -> multiline_comment ()
      )
    | _ -> Some (keyword_or_error '/')
  and single_line_comment () =
    match text_peek () with
      '~' -> text_junk (); reportShouldFail (current_loc()); single_line_comment_rest ()
    | _ -> single_line_comment_rest ()
  and single_line_comment_rest () =
    match text_peek () with
      '\010' | '\013' | '\000' -> reportRange CommentRange (current_loc())
    | c -> text_junk (); single_line_comment_rest ()
    | _ -> raise Stream.Failure
  and multiline_comment () =
    match text_peek () with
      '*' ->
      (
        text_junk ();
        (
          match text_peek () with
            '/' -> (text_junk (); reportRange CommentRange (current_loc()); next_token ())
          | _ -> multiline_comment ()
        )
      )
    | '\010' -> (text_junk (); new_loc_line (); multiline_comment ())
    | '\013' ->
      (text_junk ();
       (match text_peek () with
        | '\010' -> text_junk ()
        | _ -> ());
       new_loc_line ();
       multiline_comment ()
      )
    | '\000' when not exceptionOnError ->
      in_ghost_range := !ghost_range_start <> None;
      in_comment := true;
      reportRange CommentRange (current_loc());
      None
    | _ -> (text_junk (); multiline_comment ())
  in
  (current_loc,
   ignore_eol,
   Stream.from (fun count ->
     (try
        match next_token () with
          Some t -> Some (current_loc(), t)
        | None -> None
      with
        Stream.Error msg when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      | Stream.Failure when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      )),
   in_comment,
   in_ghost_range)

let make_lexer keywords ghostKeywords path text reportRange reportShouldFail =
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_core keywords ghostKeywords path text reportRange false false true reportShouldFail in
  (loc, ignore_eol, token_stream)

(* Region: ASTs *)

type type_ =
    Bool
  | Void
  | IntType
  | UintPtrType  (* The uintptr_t type from the C99 standard. It's an integer type big enough to hold a pointer value. *)
  | RealType
  | Char
  | StructType of string
  | PtrType of type_
  | FuncType of string   (* The name of a typedef whose body is a C function type. *)
  | InductiveType of string * type_ list
  | PredType of string list * type_ list
  | ObjType of string
  | BoxIdType (* box type, for shared boxes *)
  | HandleIdType (* handle type, for shared boxes *)
  | AnyType (* supertype of all inductive datatypes; useful in combination with predicate families *)
  | TypeParam of string (* a reference to a type parameter declared in the enclosing datatype/function/predicate *)
  | InferredType of type_ option ref (* inferred type, is unified during type checking *)

type prover_type = ProverInt | ProverBool | ProverReal | ProverInductive

(** Types as they appear in source code, before validity checking and resolution. *)
type type_expr =
    StructTypeExpr of loc * string
  | PtrTypeExpr of loc * type_expr
  | ArrayTypeExpr of loc * type_expr
  | ManifestTypeExpr of loc * type_  (* A type expression that is obviously a given type. *)
  | IdentTypeExpr of loc * string
  | ConstructedTypeExpr of loc * string * type_expr list  (* A type of the form x<T1, T2, ...> *)
  | PredTypeExpr of loc * type_expr list

(** An object used in field read expression ASTs and points-to assertion ASTs. Created by the parser and filled in by the type checker.
    TODO: Since the type checker now generates a new AST anyway, we can eliminate this hack. *)
class fieldref (name: string) =
  object
    val mutable parent: string option = None  (* Name of the struct that declares this field. *)
    val mutable range: type_ option = None  (* Declared type of the field. *)
    method name = name
    method parent = match parent with None -> assert false | Some s -> s
    method range = match range with None -> assert false | Some r -> r
    method set_parent s = parent <- Some s
    method set_range r = range <- Some r
  end

(** An object used in predicate assertion ASTs. Created by the parser and filled in by the type checker.
    TODO: Since the type checker now generates a new AST anyway, we can eliminate this hack. *)
class predref (name: string) =
  object
    val mutable tparamcount: int option = None  (* Number of type parameters. *)
    val mutable domain: type_ list option = None  (* Parameter types. *)
    val mutable inputParamCount: int option option = None  (* Number of input parameters, or None if the predicate is not precise. *)
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
  | EnumElemName of int
  | GlobalName
  | ModuleName

type
  operator = Add | Sub | Le | Lt | Eq | Neq | And | Or | Not | Mul | Div | BitNot | BitAnd | BitXor | BitOr
and
  expr =
    True of loc
  | False of loc
  | Null of loc
  | Var of loc * string * ident_scope option ref  (* An identifier. *)
  | Operation of loc * operator * expr list * type_ list option ref (* voor operaties met bovenstaande operators*)
  | IntLit of loc * big_int * type_ option ref (* int literal*)
  | StringLit of loc * string (* string literal *)
  | ClassLit of loc * string (* class literal in java *)
  | Read of loc * expr * fieldref (* lezen van een veld; hergebruiken voor java field access *)
  | Deref of loc * expr * type_ option ref (* pointee type *) (* pointer dereference *)
  | CallExpr of
      loc *
      string *
      type_expr list (* type arguments *) *
      pat list (* indices, in case this is really a predicate assertion *) *
      pat list (* arguments *) *
      func_binding
      (* oproep van functie/methode/lemma/fixpoint *)
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of
      loc *
      expr *
      switch_expr_clause list *
      (type_ * (string * type_) list * type_ list * type_) option ref (* used during evaluation when generating an anonymous fixpoint function, to get the prover types right *)
  | PredNameExpr of loc * string (* naam van predicaat en line of code*)
  | CastExpr of loc * type_expr * expr (* cast *)
  | SizeofExpr of loc * type_expr
  | AddressOf of loc * expr
  | ProverTypeConversion of prover_type * prover_type * expr  (* Generated during type checking in the presence of type parameters, to get the prover types right *)
and
  pat =
    LitPat of expr (* literal pattern *)
  | VarPat of string (* var pattern, aangeduid met ? in code *)
  | DummyPat (*dummy pattern, aangeduid met _ in code *)
and
  switch_expr_clause =
    SwitchExprClause of loc * string * string list * expr (* switch uitdrukking *)
and
  language =
    Java
  | CLang
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
    PackageDecl of loc * string * import list * decl list
and
  import =
    Import of loc * string * string option (* None betekent heel package, Some string betekent 1 ding eruit *)
and
  stmt =
    PureStmt of loc * stmt (* Statement of the form /*@ ... @*/ *)
  | NonpureStmt of loc * bool (* allowed *) * stmt  (* Nested non-pure statement; used for perform_action statements on shared boxes. *)
  | Assign of loc * string * expr (* toekenning *)
  | DeclStmt of loc * type_expr * string * expr (* enkel declaratie *)
  | Write of loc * expr * fieldref * expr (*  overschrijven van huidige waarde*)
  | WriteDeref of loc * expr * expr (* write to a pointer dereference *)
  | CallStmt of loc * string * type_expr list * expr list * func_binding (* oproep: regel - naam - type-argumenten - argumenten *)
  | IfStmt of loc * expr * stmt list * stmt list (* if  regel-conditie-branch1-branch2  *)
  | SwitchStmt of loc * expr * switch_stmt_clause list (* switch over inductief type regel-expr- constructor)*)
  | Assert of loc * pred (* assert regel-predicate *)
  | Leak of loc * pred (* expliciet lekken van assertie, nuttig op einde van thread*)
  | Open of
      loc *
      string *
      type_expr list *  (* Type arguments *)
      pat list *  (* Indices for predicate family instance, or constructor arguments for predicate constructor *)
      pat list *  (* Arguments *)
      pat option  (* Coefficient for fractional permission *)
  | Close of loc * string * type_expr list * pat list * pat list * pat option
  | ReturnStmt of loc * expr option (*return regel-return value (optie) *)
  | WhileStmt of loc * expr * pred option * stmt list * loc (* while regel-conditie-lus invariant- lus body - close brace location *)
  | BlockStmt of loc * decl list * stmt list
  | PerformActionStmt of loc * bool ref (* in non-pure context *) * string * pat list * loc * string * pat list * loc * string * expr list * bool (* atomic *) * stmt list * loc (* close brace of body *) * (loc * expr list) option * loc * string * expr list
  | SplitFractionStmt of loc * string * type_expr list * pat list * expr option (* split_fraction ... by ... *)
  | MergeFractionsStmt of loc * string * type_expr list * pat list (* merge_fraction ...*)
  | CreateBoxStmt of loc * string * string * expr list * (loc * string * string * expr list) list (* and_handle clauses *)
  | CreateHandleStmt of loc * string * string * expr
  | DisposeBoxStmt of loc * string * pat list * (loc * string * pat list) list (* and_handle clauses *)
  | LabelStmt of loc * string
  | GotoStmt of loc * string
  | NoopStmt of loc
  | InvariantStmt of loc * pred (* join point *)
  | ProduceLemmaFunctionPointerChunkStmt of loc * string * stmt option
  | ProduceFunctionPointerChunkStmt of loc * string * expr * expr list * (loc * string) list * loc * stmt list * loc
  | Throw of loc * expr
  | TryCatch of loc * stmt list * (loc * type_expr * string * stmt list) list
  | TryFinally of loc * stmt list * loc * stmt list
and
  switch_stmt_clause =
  | SwitchStmtClause of loc * string * string list * stmt list (* clause die hoort bij switch statement over constructor*)
and
  pred = (* A separation logic assertion *)
    Access of loc * expr * fieldref * pat (*  toegang tot veld regel-expr-veld-pattern*)
  | CallPred of loc * predref * type_expr list * pat list (* indices of predicate family instance *) * pat list  (* Predicate assertion, before type checking *)
  | WCallPred of loc * predref * type_ list * pat list * pat list  (* Predicate assertion, after type checking. (W is for well-formed) *)
  | ExprPred of loc * expr (*  uitdrukking regel-expr *)
  | Sep of loc * pred * pred  (* separate conjunction *)
  | IfPred of loc * expr * pred * pred (* if-predicate in de vorm expr? p1:p2 regel-expr-p1-p2 *)
  | SwitchPred of loc * expr * switch_pred_clause list (* switch over cons van inductive type regel-expr-clauses*)
  | EmpPred of loc (* als "emp" bij requires/ensures staat -regel-*)
  | CoefPred of loc * pat * pred (* fractional permission met coeff-predicate*)
and
  switch_pred_clause =
  | SwitchPredClause of loc * string * string list * prover_type option list option ref (* Boxing info *) * pred (*  clauses bij switch  regel-cons-lijst v var in cons- body*)
and
  func_kind =
  | Regular
  | Fixpoint
  | Lemma
and
  meth =
  | Meth of loc * type_expr option * string * (type_expr * string) list * (pred * pred) option * (stmt list * loc (* Close brace *)) option * func_binding * visibility
and
  meth_spec =
  | MethSpec of loc * type_expr option * string * (type_expr * string) list * (pred * pred) option* func_binding * visibility
and
  cons =
  | Cons of loc * (type_expr * string) list * (pred * pred) option * (stmt list * loc (* Close brace *)) option * visibility
and
  decl =
    Struct of loc * string * field list option
  | Inductive of loc * string * string list * ctor list (* inductief data type regel-naam-type parameters-lijst van constructors*)
  | Class of loc * string * meth list * field list *cons list* string * string list(* laatste 2 strings zijn naam v superklasse en lijst van namen van interfaces*)
  | Interface of loc * string * meth_spec list
  | PredFamilyDecl of loc * string * string list (* type parameters *) * int (* number of indices *) * type_expr list * int option (* (Some n) means the predicate is precise and the first n parameters are input parameters *)
  | PredFamilyInstanceDecl of loc * string * string list (* type parameters *) * (loc * string) list * (type_expr * string) list * pred
  | PredCtorDecl of loc * string * (type_expr * string) list * (type_expr * string) list * pred
  | Func of
      loc *
      func_kind *
      string list *  (* type parameters *)
      type_expr option *  (* return type *)
      string *  (* name *)
      (type_expr * string) list *  (* parameters *)
      bool (* atomic *) *
      (string * (loc * string) list) option (* implemented function type, with function type arguments *) *
      (pred * pred) option *  (* contract *)
      (stmt list * loc (* Close brace *)) option *  (* body *)
      func_binding *  (* static or instance *)
      visibility
  | FuncTypeDecl of loc * ghostness * type_expr option * string * (type_expr * string) list * (type_expr * string) list * (pred * pred)
  | BoxClassDecl of loc * string * (type_expr * string) list * pred * action_decl list * handle_pred_decl list
  (* enum def met line - name - elements *)
  | EnumDecl of loc * string * (string list)
  | Global of loc * type_expr * string * (expr option)
  | UnloadableModuleDecl of loc
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
  | Field of loc * ghostness * type_expr * string * func_binding * visibility  (* veld met regel-type-naam*)
and
  ctor =
  | Ctor of loc * string * type_expr list (* constructor met regel-naam-lijst v types v args*)
and
  member = FieldMember of field | MethMember of meth | ConsMember of cons

(* Region: some AST inspector functions *)

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
  | CallPred (l, g, targs, ies, es) -> l
  | WCallPred (l, g, targs, ies, es) -> l
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
  | Open (l, _, _, _, _, coef) -> l
  | Close (l, _, _, _, _, coef) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _, _) -> l
  | Throw (l, _) -> l
  | TryCatch (l, _, _) -> l
  | TryFinally (l, _, _, _) -> l
  | BlockStmt (l, ds, ss) -> l
  | PerformActionStmt (l, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> l
  | SplitFractionStmt (l, _, _, _, _) -> l
  | MergeFractionsStmt (l, _, _, _) -> l
  | CreateBoxStmt (l, _, _, _, _) -> l
  | CreateHandleStmt (l, _, _, _) -> l
  | DisposeBoxStmt (l, _, _, _) -> l
  | LabelStmt (l, _) -> l
  | GotoStmt (l, _) -> l
  | NoopStmt l -> l
  | InvariantStmt (l, _) -> l
  | ProduceLemmaFunctionPointerChunkStmt (l, _, _) -> l
  | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) -> l

let type_expr_loc t =
  match t with
    ManifestTypeExpr (l, t) -> l
  | StructTypeExpr (l, sn) -> l
  | IdentTypeExpr (l, x) -> l
  | ConstructedTypeExpr (l, x, targs) -> l
  | PtrTypeExpr (l, te) -> l
  | ArrayTypeExpr(l,te) -> l
  | PredTypeExpr(l,te) ->l

(* Region: the parser *)

let common_keywords = [
  "switch"; "case"; ":"; "return";
  "void"; "if"; "else"; "while"; "!="; "<"; ">"; "<="; ">="; "&&"; "++"; "--"; "+="; "-=";
  "||"; "!"; "["; "]"; "{";
  "}"; ";"; "int"; "true"; "false"; "("; ")"; ","; "="; "|"; "+"; "-"; "=="; "?";
  "*"; "/"; "&"; "^"; "~"; "assert"; "currentCodeFraction"; "currentThread"
]

let ghost_keywords = [
  "predicate"; "requires"; "|->"; "&*&"; "inductive"; "fixpoint";
  "ensures"; "close"; "lemma"; "open"; "emp"; "invariant";
  "forall"; "_"; "@*/"; "predicate_family"; "predicate_family_instance"; "predicate_ctor"; "leak"; "@";
  "box_class"; "action"; "handle_predicate"; "preserved_by"; "consuming_box_predicate"; "consuming_handle_predicate"; "perform_action"; "atomic";
  "create_box"; "and_handle"; "create_handle"; "dispose_box"; "produce_lemma_function_pointer_chunk"; "produce_function_pointer_chunk";
  "producing_box_predicate"; "producing_handle_predicate"; "box"; "handle"; "any"; "real"; "split_fraction"; "by"; "merge_fractions";
  "unloadable_module"
]

let c_keywords = [
  "struct"; "bool"; "char"; "->"; "sizeof"; "typedef"; "#"; "include"; "ifndef";
  "define"; "endif"; "&"; "goto"; "uintptr_t"; "INT_MIN"; "INT_MAX"; "UINTPTR_MAX"; "enum"; "static"
]

let java_keywords = [
  "public"; "char"; "private"; "protected"; "class"; "."; "static"; "boolean"; "new"; "null"; "interface"; "implements"; "package"; "import"; "*";
  "throw"; "try"; "catch"; "throws"
]

let file_type path=
  begin
  if Filename.check_suffix (Filename.basename path) ".c" then CLang
  else if Filename.check_suffix (Filename.basename path) ".jarsrc" then Java
  else if Filename.check_suffix (Filename.basename path) ".jarspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".java" then Java
  else if Filename.check_suffix (Filename.basename path) ".javaspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".scala" then Java
  else if Filename.check_suffix (Filename.basename path) ".h" then CLang
  else failwith ("unknown extension")
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

type spec_clause =
  AtomicClause
| FuncTypeClause of string * (loc * string) list
| RequiresClause of pred
| EnsuresClause of pred

(* A toy Scala parser. *)
module Scala = struct

  let keywords = [
    "def"; "var"; "class"; "object"; "."; "new"; "null"; "package"; "import";
    "+"; "="; "("; ")"; ":"; "{"; "}"; "["; "]"; "/*@"; "@*/"; "=="; "="; ";"; "true"; "false"; "assert"
  ]

  let rec
    parse_decl = parser
      [< '(l, Kwd "object"); '(_, Ident cn); '(_, Kwd "{"); ms = rep parse_method; '(_, Kwd "}") >] ->
      Class (l, cn, ms, [], [], "Object", [])
  and
    parse_method = parser
      [< '(l, Kwd "def"); '(_, Ident mn); ps = parse_paramlist; t = parse_type_ann; co = parse_contract; '(_, Kwd "=");'(_, Kwd "{"); ss = rep parse_stmt; '(closeBraceLoc, Kwd "}")>] ->
      let rt = match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t in
      Meth (l, rt, mn, ps, Some co,Some (ss, closeBraceLoc), Static, Public)
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
    parse_stmt = parser
      [< '(l, Kwd "var"); '(_, Ident x); t = parse_type_ann; '(_, Kwd "="); e = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, t, x, e)
    | [< '(l, Kwd "assert"); a = parse_asn; '(_, Kwd ";") >] -> Assert (l, a)

end

(* The C/Java parser.
   The difference is in the scanner: when parsing a C file, the scanner treats "class" like an identifier, not a keyword.
   And Kwd "class" does not match Ident "class".
   *)
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
  (*[<'(_, Kwd "extends");'(_, Ident s)>] -> s 
|*) [<>] -> "Object"
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
  parse_qualified_identifier = parser
  [< '(l, Ident x); xs = rep (parser [< '(_, Kwd "."); '(l, Ident x) >] -> (l, x)) >] -> (l, x)::xs
and
  parse_throws_clause = parser
  [< '(l, Kwd "throws"); _ = rep_comma parse_qualified_identifier >] -> ()
and
  parse_java_member vis cn= parser
  [< '(l, Kwd "static");t=parse_return_type;'(_,Ident n);
    ps = parse_paramlist;
    _ = opt parse_throws_clause;
    (ss, co) = parser
      [< '(_, Kwd ";"); co = opt parse_spec >] -> (None, co)
    | [< co = opt parse_spec; ss = parse_some_block >] -> (ss, co)
    >] -> MethMember(Meth(l,t,n,ps,co,ss,Static,vis))
| [<'(l,Ident t);e=parser
    [<'(_,Ident f);r=parser
      [<'(_, Kwd ";")>]->FieldMember(Field (l,Real,IdentTypeExpr(l,t),f,Instance,vis))
    | [< ps = parse_paramlist;
         _ = opt parse_throws_clause;
         (ss,co)=parser
        [<'(_, Kwd ";");co = opt parse_spec>]-> (None,co)
      | [<co = opt parse_spec;ss=parse_some_block>] -> (ss,co)
    >] -> MethMember(Meth(l,Some (IdentTypeExpr(l,t)),f,(IdentTypeExpr(l,cn),"this")::ps,co,ss,Instance,vis))
    >] -> r
  | [< ps = parse_paramlist;
       _ = opt parse_throws_clause;
       i=parser
      [<'(_, Kwd ";");co = opt parse_spec>]-> ConsMember(Cons(l,ps,co,None,vis))
    | [<co = opt parse_spec; ss=parse_some_block>]-> ConsMember(Cons(l,ps,co,ss,vis))
   >]-> i
 >] -> e
| [< t=parse_return_type;'(l,Ident f);r=parser
    [<'(_, Kwd ";")>] ->
      (match t with 
        None -> raise (ParseException (l, "Invalid type of field")) 
      | Some t -> FieldMember(Field (l,Real,t,f,Instance,vis)))
  | [< ps = parse_paramlist;
       _ = opt parse_throws_clause;
      (ss,co)=parser
      [<'(_, Kwd ";");co = opt parse_spec>]-> (None,co)
    | [<co = opt parse_spec; ss=parse_some_block>] -> (ss,co)
    >] -> 
      MethMember(Meth(l,t,f,(IdentTypeExpr(l,cn),"this")::ps,co,ss,Instance,vis))
>] -> r
and
  parse_functype_paramlists = parser
  [< ps1 = parse_paramlist; ps2 = opt parse_paramlist >] -> (match ps2 with None -> ([], ps1) | Some ps2 -> (ps1, ps2))
| [< '(_, Kwd "/*@"); ps1 = parse_paramlist; '(_, Kwd "@*/"); ps2 = parse_paramlist >] -> (ps1, ps2)
and
  parse_decl = parser
  [< '(l, Kwd "struct"); '(_, Ident s); d = parser
    [< '(_, Kwd "{"); fs = parse_fields; '(_, Kwd ";") >] -> Struct (l, s, Some fs)
  | [< '(_, Kwd ";") >] -> Struct (l, s, None)
  | [< t = parse_type_suffix (StructTypeExpr (l, s)); d = parse_func_rest Regular (Some t) >] -> d
  >] -> [d]
| [< '(l, Kwd "typedef"); rt = parse_return_type; '(_, Ident g); (ftps, ps) = parse_functype_paramlists; '(_, Kwd ";"); c = parse_spec >]
  -> [FuncTypeDecl (l, Real, rt, g, ftps, ps, c)]
| [< '(_, Kwd "enum"); '(l, Ident n); '(_, Kwd "{"); elems = (rep_comma (parser [< '(_, Ident e) >] -> e)); '(_, Kwd "}"); '(_, Kwd ";"); >] -> [EnumDecl(l, n, elems)]
| [< '(_, Kwd "static"); t = parse_type; '(l, Ident x); '(_, Kwd ";") >] -> [Global(l, t, x, None)] (* assumes globals start with keyword static *)
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
  parse_pred_body = parser
    [< '(_, Kwd "requires"); p = parse_pred >] -> p
  | [< '(_, Kwd "="); p = parse_pred >] -> p
and
  parse_pure_decl = parser
    [< '(l, Kwd "inductive"); '(li, Ident i); tparams = parse_type_params li; '(_, Kwd "="); cs = (parser [< cs = parse_ctors >] -> cs | [< cs = parse_ctors_suffix >] -> cs); '(_, Kwd ";") >] -> [Inductive (l, i, tparams, cs)]
  | [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> [d]
  | [< '(l, Kwd "predicate"); '(li, Ident g); tparams = parse_type_params li; '(_, Kwd "("); ps = rep_comma parse_param;
     (ps, inputParamCount) = (parser [< '(_, Kwd ";"); ps' = rep_comma parse_param >] -> (ps @ ps', Some (List.length ps)) | [< >] -> (ps, None));
     '(_, Kwd ")");
     body = opt parse_pred_body;
     '(_, Kwd ";");
    >] ->
    [PredFamilyDecl (l, g, tparams, 0, List.map (fun (t, p) -> t) ps, inputParamCount)] @
    (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
  | [< '(l, Kwd "predicate_family"); '(_, Ident g); is = parse_paramlist; ps = parse_paramlist; '(_, Kwd ";") >]
  -> [PredFamilyDecl (l, g, [], List.length is, List.map (fun (t, p) -> t) ps, None)]
  | [< '(l, Kwd "predicate_family_instance"); '(_, Ident g); is = parse_index_list; ps = parse_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredFamilyInstanceDecl (l, g, [], is, ps, p)]
  | [< '(l, Kwd "predicate_ctor"); '(_, Ident g); ps1 = parse_paramlist; ps2 = parse_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredCtorDecl (l, g, ps1, ps2, p)]
  | [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest Lemma t >] -> [d]
  | [< '(l, Kwd "box_class"); '(_, Ident bcn); ps = parse_paramlist;
       '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";");
       ads = parse_action_decls; hpds = parse_handle_pred_decls; '(_, Kwd "}") >] -> [BoxClassDecl (l, bcn, ps, inv, ads, hpds)]
  | [< '(l, Kwd "typedef"); '(_, Kwd "lemma"); rt = parse_return_type; '(_, Ident g); (ftps, ps) = parse_functype_paramlists; '(_, Kwd ";"); c = parse_spec >] ->
    [FuncTypeDecl (l, Ghost, rt, g, ftps, ps, c)]
  | [< '(l, Kwd "unloadable_module"); '(_, Kwd ";") >] -> [UnloadableModuleDecl l]
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
| [< '(l, Kwd "enum"); '(_, Ident _) >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "int") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "uintptr_t") >] -> ManifestTypeExpr (l, UintPtrType)
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
  parse_functypeclause_args = parser
  [< '(_, Kwd "("); args = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")") >] -> args
| [< >] -> []
and
  parse_pure_spec_clause = parser
  [< '(_, Kwd "atomic") >] -> AtomicClause
| [< '(_, Kwd ":"); '(_, Ident ft); ftargs = parse_functypeclause_args >] -> FuncTypeClause (ft, ftargs)
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
    let ft = (parser [< 'FuncTypeClause (ft, ftargs) >] -> out_count := !out_count + 1; Some (ft, ftargs) | [< >] -> None) clause_stream in
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
  [< '(l, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] -> Some (ss,closeBraceLoc)
| [<>] -> None
and
  parse_block_stmt = parser
  [< '(l, Kwd "{");
     b = (parser
       [< '((sp1, _), Kwd "/*@");
          b = parser
            [< s = parse_stmt0; '((_, sp2), Kwd "@*/"); ss = parse_stmts >] -> BlockStmt (l, [], PureStmt ((sp1, sp2), s)::ss)
          | [< ds = parse_pure_decls; '(_, Kwd "@*/"); ss = parse_stmts >] -> BlockStmt (l, ds, ss)
       >] -> b
     | [< ds = parse_pure_decls; ss = parse_stmts >] -> BlockStmt (l, ds, ss));
     '(_, Kwd "}")
  >] -> b
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
     CallExpr (_, g, targs, es1, es2,_) -> Open (l, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [< '(l, Kwd "close"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, targs, es1, es2,_) -> Close (l, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of close statement must be call expression.")))
| [< '(l, Kwd "split_fraction"); '(li, Ident p); targs = parse_type_args li; pats = parse_patlist;
     coefopt = (parser [< '(_, Kwd "by"); e = parse_expr >] -> Some e | [< >] -> None);
     '(_, Kwd ";") >] -> SplitFractionStmt (l, p, targs, pats, coefopt)
| [< '(l, Kwd "merge_fractions"); '(li, Ident p); targs = parse_type_args li; pats = parse_patlist; '(_, Kwd ";") >]
  -> MergeFractionsStmt (l, p, targs, pats)
| [< '(l, Kwd "dispose_box"); '(_, Ident bcn); pats = parse_patlist;
     handleClauses = rep (parser [< '(l, Kwd "and_handle"); '(_, Ident hpn); pats = parse_patlist >] -> (l, hpn, pats));
     '(_, Kwd ";") >] -> DisposeBoxStmt (l, bcn, pats, handleClauses)
| [< '(l, Kwd "create_box"); '(_, Ident x); '(_, Kwd "="); '(_, Ident bcn); args = parse_arglist;
     handleClauses = rep (parser [< '(l, Kwd "and_handle"); '(_, Ident x); '(_, Kwd "="); '(_, Ident hpn); args = parse_arglist >] -> (l, x, hpn, args));
     '(_, Kwd ";")
     >] -> CreateBoxStmt (l, x, bcn, args, handleClauses)
| [< '(l, Kwd "produce_lemma_function_pointer_chunk"); '(_, Kwd "("); '(_, Ident x); '(_, Kwd ")");
     body = parser
       [< '(_, Kwd ";") >] -> None
     | [< s = parse_stmt >] -> Some s
  >] -> ProduceLemmaFunctionPointerChunkStmt (l, x, body)
| [< '(l, Kwd "produce_function_pointer_chunk"); '(_, Ident ftn);
     '(_, Kwd "("); fpe = parse_expr; '(_, Kwd ")");
     args = parse_arglist;
     '(_, Kwd "("); params = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")");
     '(openBraceLoc, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
  ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc)
| [< '(l, Kwd "goto"); '(_, Ident lbl); '(_, Kwd ";") >] -> GotoStmt (l, lbl)
| [< '(l, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";") >] -> InvariantStmt (l, inv)
| [< '(l, Kwd "return"); eo = parser [< '(_, Kwd ";") >] -> None | [< e = parse_expr; '(_, Kwd ";") >] -> Some e >] -> ReturnStmt (l, eo)
| [< '(l, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     inv = opt (parser [< '((sp1, _), Kwd "/*@"); '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '((_, sp2), Kwd "@*/") >] -> p);
     '(_, Kwd "{"); b = parse_stmts; '(closeBraceLoc, Kwd "}") >] -> WhileStmt (l, e, inv, b, closeBraceLoc)
| [< '(l, Kwd "throw"); e = parse_expr; '(_, Kwd ";") >] -> Throw (l, e)
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
| [< '(l, Kwd ";") >] -> NoopStmt l
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] ->
      (match e with
        CallExpr (l, g, targs, [], es,fb) ->
          let unpack_LitPat x =
            match x with
            | LitPat e -> e
            | VarPat x -> raise (ParseException (expr_loc e, Printf.sprintf "No variable patterns (?%s) allowed in call expression." x))
            | DummyPat -> raise (ParseException (expr_loc e, "No dummy patterns allowed in call expression."))
          in
          CallStmt (l, g, targs, List.map unpack_LitPat es, fb)
       | _ -> raise (ParseException (expr_loc e, "An expression used as a statement must be a call expression.")))
  | [< '(l, Kwd ":") >] -> (match e with Var (_, lbl, _) -> LabelStmt (l, lbl) | _ -> raise (ParseException (l, "Label must be identifier.")))
  | [< '(l, Kwd "="); rhs = parse_expr; '(_, Kwd ";") >] ->
    begin match e with
      Operation (llhs, Mul, [Var (lt, t, _); Var (lx, x, _)], _) ->
      DeclStmt (l, PtrTypeExpr (llhs, IdentTypeExpr (lt, t)), x, rhs)
    | _ -> assignment_stmt l e rhs
    end
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
     | CallExpr (l, g, targs, pats0, pats,_) -> CallPred (l, new predref g, targs, pats0, pats)
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
  [< e0 = parse_bitor_expr; e = parse_expr_conj_rest e0 >] -> e
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
| [< '(l, CharToken c) >] -> IntLit(l, big_int_of_int (Char.code c), ref (Some Char))
| [< '(l, Kwd "null") >] -> Null l
| [< '(l, Kwd "currentThread") >] -> Var (l, "currentThread", ref None)
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
| [< '(l, Kwd "INT_MIN") >] -> IntLit (l, big_int_of_string "-2147483648", ref None)
| [< '(l, Kwd "INT_MAX") >] -> IntLit (l, big_int_of_string "2147483647", ref None)
| [< '(l, Kwd "UINTPTR_MAX") >] -> IntLit (l, big_int_of_string "4294967295", ref None)
| [< '(l, String s); ss = rep (parser [< '(_, String s) >] -> s) >] -> StringLit (l, String.concat "" (s::ss))
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
| [< '(l, Kwd "~"); e = parse_expr_suffix >] -> Operation (l, BitNot, [e], ref None)
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
  
let parse_import0= parser
  [<'(l, Kwd "import");n= parse_import_name>] -> let (pn,el)=n in Import(l,pn,el)

let parse_import = parser
  [< i = parse_import0 >] -> i
| [< i = peek_in_ghost_range (parser [< i = parse_import0; '(_, Kwd "@*/") >] -> i) >] -> i

let parse_package_decl= parser
  [< (l,p) = parse_package; is=rep parse_import; ds=parse_decls;>] -> PackageDecl(l,p,Import(dummy_loc,"java.lang",None)::is,ds)

let parse_scala_file (path: string) (reportRange: range_kind -> loc -> unit): package =
  let lexer = make_lexer Scala.keywords ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< ds = rep Scala.parse_decl; _ = Stream.empty >] -> PackageDecl(dummy_loc,"",[Import(dummy_loc,"java.lang",None)],ds) in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_java_file (path: string) (reportRange: range_kind -> loc -> unit): package =
  if Filename.check_suffix (Filename.basename path) ".scala" then
    parse_scala_file path reportRange
  else
  let lexer = make_lexer (common_keywords @ java_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< p = parse_package_decl; _ = Stream.empty >] -> p in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

type 'result parser_ = (loc * token) Stream.t -> 'result

let parse_include_directives (ignore_eol: bool ref): (loc * string) list parser_ =
  let rec parse_include_directives = parser
    [< header = parse_include_directive; headers = parse_include_directives >] -> header::headers
  | [< >] -> []
  and
  parse_include_directive = parser
    [< '(_, Kwd "#"); _ = (fun _ -> ignore_eol := false); '(_, Kwd "include"); '(l, String header); '(_, Eol) >] -> ignore_eol := true; (l, header)
  | [< d = peek_in_ghost_range (parser [< '(_, Kwd "#"); '(_, Kwd "include"); '(l, String header); '(_, Kwd "@*/") >] -> (l, header)) >] -> d
in
  parse_include_directives

let parse_c_file (path: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit): ((loc * string) list * package list) =
  let lexer = make_lexer (common_keywords @ c_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange reportShouldFail in
  let parse_c_file =
    parser
      [< headers = parse_include_directives ignore_eol; ds = parse_decls; _ = Stream.empty >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
  in
  try
    parse_c_file token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_header_file (basePath: string) (relPath: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit): ((loc * string) list * package list) =
  let lexer = make_lexer (common_keywords @ c_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (readFile (Filename.concat basePath relPath)) reportRange reportShouldFail in
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
  let lexer = make_lexer ["."] [] in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (readFile (Filename.concat basePath relPath)) reportRange (fun _ -> ()) in
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
  let lexer = make_lexer [".";"-"] [] in
  let (loc, ignore_eol, token_stream) = lexer (basePath, relPath) (readFile (Filename.concat basePath relPath)) reportRange (fun _ -> ()) in
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

(* Region: some auxiliary types and functions *)

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

exception StaticError of loc * string

let static_error l msg = raise (StaticError (l, msg))

(** Internal pattern. Either a pattern from the source code, or a term pattern. A term pattern (TermPat t) matches a term t' if t and t' are definitely_equal. *)
type 'termnode pat0 = SrcPat of pat | TermPat of 'termnode
(** A heap chunk. *)
type 'termnode chunk =
  Chunk of
    ('termnode (* Predicate name *) * bool (* true if a declared predicate's symbol; false in a scenario where predicate names are passed as values. Used to avoid prover queries. *) ) *
    type_ list *  (* Type arguments *)
    'termnode *  (* Coefficient of fractional permission *)
    'termnode list *  (* Arguments; their prover type is as per the instantiated parameter types, not the generic ones. *)
    int option  (* Size of this chunk with respect to the first chunk of the precondition; used to check lemma termination. *)
type 'termnode heap = 'termnode chunk list
type 'termnode env = (string * 'termnode) list
(** Execution trace. For error reporting. *)
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext

(* Returns the locations of the "call stack" of the current execution step. *)
let get_callers (ctxts: 'termnode context list): loc option list =
  let rec iter lo ls ctxts =
    match ctxts with
      [] -> ls
    | Executing (_, _, l, _)::ctxts -> iter (Some l) ls ctxts
    | PushSubcontext::ctxts -> iter lo (lo::ls) ctxts
    | PopSubcontext::ctxts -> let ls = match ls with [] -> [] | _::ls -> ls in iter None ls ctxts
    | _::ctxts -> iter lo ls ctxts
  in
  iter None [] (List.rev ctxts)

let get_root_caller ctxts = match List.rev (get_callers ctxts) with Some l::_ -> Some l | _ -> None

let rec string_of_type t =
  match t with
    Bool -> "bool"
  | Void -> "void"
  | IntType -> "int"
  | UintPtrType -> "uintptr_t"
  | RealType -> "real"
  | Char -> "char"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
  | ObjType l -> "class " ^ l
  | StructType sn -> "struct " ^ sn
  | PtrType t -> string_of_type t ^ " *"
  | FuncType ft -> ft
  | PredType (tparams, ts) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    Printf.sprintf "predicate%s(%s)" tparamsText (String.concat ", " (List.map string_of_type ts))
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | TypeParam x -> x
  | InferredType t -> begin match !t with None -> "?" | Some t -> string_of_type t end

let string_of_targs targs =
  if targs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"

(* This assumes the termnodes have already been converted to strings. *)
let string_of_chunk (Chunk ((g, literal), targs, coef, ts, size): string chunk): string =
  (if coef = "1" then "" else "[" ^ coef ^ "]") ^ g ^ string_of_targs targs ^ "(" ^ String.concat ", " ts ^ ")"

let string_of_heap h = String.concat " * " (List.map string_of_chunk h)

let string_of_context c =
  match c with
    Assuming t -> "Assuming " ^ t
  | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s
  | PushSubcontext -> "Entering subcontext"
  | PopSubcontext -> "Leaving subcontext"

exception SymbolicExecutionError of string context list * string * loc * string

let full_name pn n = if pn = "" then n else pn ^ "." ^ n

let zip xs ys =
  let rec iter xs ys zs =
    match (xs, ys) with
      ([], []) -> Some (List.rev zs)
    | (x::xs, y::ys) -> iter xs ys ((x, y)::zs)
    | _ -> None
  in
  iter xs ys []
  
let rec zip2 xs ys =
  match (xs, ys) with
    ([], _) -> []
  | (_, []) -> []
  | (x :: xs, y :: ys) -> (x, y) :: (zip2 xs ys)

let do_finally tryBlock finallyBlock =
  let result =
    try
      tryBlock()
    with e -> finallyBlock(); raise e
  in
  finallyBlock();
  result

type options = {option_verbose: bool; option_disable_overflow_check: bool; option_allow_should_fail: bool; option_emit_manifest: bool}

(* Region: verify_program_core: the toplevel function *)

(** Verifies the .c/.jarsrc/.scala file at path [path].
    Uses the SMT solver [ctxt].
    Reports syntax highlighting regions using the callback [reportRange].
    Stops at source line [breakpoint], if not None.
    This function is generic in the types of SMT solver types, symbols, and terms.
    *)
let verify_program_core (ctxt: ('typenode, 'symbol, 'termnode) Proverapi.context) options path reportRange breakpoint =

  let language = file_type path in

  let {
    option_verbose=verbose;
    option_disable_overflow_check=disable_overflow_check;
    option_allow_should_fail=allow_should_fail;
    option_emit_manifest=emit_manifest
  } = options in
  let verbose_print_endline s = if verbose then print_endline s else () in
  let verbose_print_string s = if verbose then print_string s else () in

  (** The set of currently used SMT solver symbol identifiers. Used to generate fresh SMT solver symbols. *)
  let used_ids = ref [] in
  (** The terms that represent coefficients of leakable chunks. These come from [_] patterns in the source code. *)
  let dummy_frac_terms = ref [] in
  (** When switching to the next symbolic execution branch, this stack is popped to forget about fresh identifiers generated in the old branch. *)
  let used_ids_stack = ref [] in

  (** Remember the current path condition, set of used IDs, and set of dummy fraction terms. *)  
  let push() =
    used_ids_stack := (!used_ids, !dummy_frac_terms)::!used_ids_stack;
    ctxt#push
  in
  
  (** Restore the previous path condition, set of used IDs, and set of dummy fraction terms. *)
  let pop() =
    let ((ids, dummyFracTerms)::t) = !used_ids_stack in
    used_ids := ids;
    dummy_frac_terms := dummyFracTerms;
    used_ids_stack := t;
    ctxt#pop
  in
  
  (** Execute [cont] in a temporary context. *)
  let in_temporary_context cont =
    push();
    cont();
    pop()
  in
  
  (** Generate a fresh ID based on string [s]. *)
  let mk_ident s =
    let rec iter k =
      let sk = s ^ string_of_int k in
      if List.mem sk !used_ids then iter (k + 1) else (used_ids := sk::!used_ids; sk)
    in
    let name = if List.mem s !used_ids then iter 0 else (used_ids := s::!used_ids; s) in
    name
  in

  (** Generate a fresh SMT solver symbol based on string [s]. *)  
  let mk_symbol s domain range kind =
    ctxt#mk_symbol (mk_ident s) domain range kind
  in
  
  let alloc_nullary_ctor j s = mk_symbol s [] ctxt#type_inductive (Proverapi.Ctor (CtorByOrdinal j)) in

  (* Region: boxing and unboxing *)
  
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
    | UintPtrType -> ProverInt
    | RealType -> ProverReal
    | Char -> ProverInt
    | InductiveType _ -> ProverInductive
    | StructType sn -> assert false
    | ObjType n -> ProverInt
    | PtrType t -> ProverInt
    | FuncType _ -> ProverInt
    | PredType (tparams, ts) -> ProverInductive
    | BoxIdType -> ProverInt
    | HandleIdType -> ProverInt
    | AnyType -> ProverInductive
    | TypeParam _ -> ProverInductive
    | Void -> ProverInductive
    | InferredType t -> begin match !t with None -> t := Some (InductiveType ("unit", [])); ProverInductive | Some t -> provertype_of_type t end
  in
  
  let typenode_of_type t = typenode_of_provertype (provertype_of_type t) in
  
  let get_unique_var_symb x t = ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) [] in
  
  let get_dummy_frac_term () =
    let t = get_unique_var_symb "dummy" RealType in
    dummy_frac_terms := t::!dummy_frac_terms;
    t
  in
  
  let is_dummy_frac_term t = List.memq t !dummy_frac_terms in
  
  let get_unique_var_symbs xts = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) xts in
  
  (* Generate some global symbols. *)
  
  let get_class_symbol = mk_symbol "getClass" [ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_or_symbol = mk_symbol "bitor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_xor_symbol = mk_symbol "bitxor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_and_symbol = mk_symbol "bitand" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_not_symbol = mk_symbol "bitnot" [ctxt#type_int] ctxt#type_int Uninterp in
  
  let boolt = Bool in
  let intt = IntType in

  let real_zero = ctxt#mk_reallit 0 in
  let real_unit = ctxt#mk_reallit 1 in
  let real_half = ctxt#mk_reallit_of_num (num_of_ints 1 2) in
  
  let min_int_big_int = big_int_of_string "-2147483648" in
  let min_int_term = ctxt#mk_intlit_of_string "-2147483648" in
  let max_int_big_int = big_int_of_string "2147483647" in
  let max_int_term = ctxt#mk_intlit_of_string "2147483647" in
  let max_ptr_big_int = big_int_of_string "4294967295" in
  let max_ptr_term = ctxt#mk_intlit_of_string "4294967295" in
  let min_char_big_int = big_int_of_string "-128" in
  let min_char_term = ctxt#mk_intlit_of_string "-128" in
  let max_char_big_int = big_int_of_string "127" in
  let max_char_term = ctxt#mk_intlit_of_string "127" in
  
  let real_unit_pat = TermPat real_unit in
  
  let current_module_name = Filename.chop_extension (Filename.basename path) in
  let current_module_term = get_unique_var_symb current_module_name IntType in
  let modulemap = [(current_module_name, current_module_term)] in

  (** Convert term [t] from type [proverType] to type [proverType0]. *)  
  let apply_conversion proverType proverType0 t =
    match (proverType, proverType0) with
    | (ProverBool, ProverInductive) -> ctxt#mk_boxed_bool t
    | (ProverInt, ProverInductive) -> ctxt#mk_boxed_int t
    | (ProverReal, ProverInductive) -> ctxt#mk_boxed_real t
    | (ProverInductive, ProverBool) -> ctxt#mk_unboxed_bool t
    | (ProverInductive, ProverInt) -> ctxt#mk_unboxed_int t
    | (ProverInductive, ProverReal) -> ctxt#mk_unboxed_real t
  in

  let programDir = Filename.dirname path in
  let preludePath = Filename.concat bindir "prelude.h" in
  let rtdir= Filename.concat bindir "rt" in 
  let rtpath= Filename.concat rtdir "rt.jarspec" in
  (** Records the source lines containing //~, indicating that VeriFast is supposed to detect an error on that line. *)
  let shouldFailLocs = ref [] in
  
  (* Callback function called from the lexer. *)
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
    let loc_of_ctxts ctxts l = match get_root_caller ctxts with None -> l | Some l -> l in
    try
      body ()
    with
    | StaticError (l, msg) when should_fail l -> has_failed l
    | SymbolicExecutionError (ctxts, phi, l, msg) when should_fail (loc_of_ctxts ctxts l) -> has_failed (loc_of_ctxts ctxts l)
  in

  (* Maps a header file name to the list of header file names that it includes, and the various maps of VeriFast elements that it declares directly. *)
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
  
  (* Region: check_file *)

  (** Verify the .c/.h/.jarsrc/.jarspec file whose headers are given by [headers] and which declares packages [ps].
      As a side-effect, adds all processed headers to the header map.
      Recursively calls itself on headers included by the current file.
      Returns the elements declared directly in the current file.
      May add symbols and global assumptions to the SMT solver.
    *)      
  let rec check_file include_prelude basedir headers ps =
  let (structmap0, enummap0, globalmap0, inductivemap0, purefuncmap0,predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0,boxmap0,classmap0,interfmap0) =
  
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
    let merge_maps l
      (structmap, enummap, globalmap, inductivemap, purefuncmap, predctormap, fixpointmap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, functypemap, funcmap, boxmap, classmap, interfmap)
      (structmap0, enummap0, globalmap0, inductivemap0, purefuncmap0, predctormap0, fixpointmap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, functypemap0, funcmap0, boxmap0, classmap0, interfmap0)
      =
      (append_nodups structmap structmap0 id l "struct",
       append_nodups enummap enummap0 id l "enum",
       append_nodups globalmap globalmap0 id l "global variable",
       append_nodups inductivemap inductivemap0 id l "inductive datatype",
       append_nodups purefuncmap purefuncmap0 id l "pure function",
       append_nodups predctormap predctormap0 id l "predicate constructor",
       append_nodups fixpointmap fixpointmap0 id l "fixpoint function",
       malloc_block_pred_map @ malloc_block_pred_map0,
       field_pred_map @ field_pred_map0,
       append_nodups predfammap predfammap0 id l "predicate",
       append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance",
       append_nodups functypemap functypemap0 id l "function type",
       append_nodups funcmap funcmap0 id l "function",
       append_nodups boxmap boxmap0 id l "box predicate",
       append_nodups classmap classmap0 id l "class",
       append_nodups interfmap interfmap0 id l "interface")
    in

    (** [merge_header_maps maps0 headers] returns [maps0] plus all elements transitively declared in [headers]. *)
    let rec merge_header_maps include_prelude maps0 headers_included headers =
      match headers with
        [] -> (maps0, headers_included)
      | (l, header_path)::headers ->
    if file_type path <> Java then
        if List.mem header_path ["bool.h"; "assert.h"] then
          merge_header_maps include_prelude maps0 headers_included headers
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
          if List.mem path headers_included then
            merge_header_maps include_prelude maps0 headers_included headers
          else
          begin
            let (headers', maps) =
              match try_assoc path !headermap with
                None ->
                let (headers', ds) = parse_header_file basedir relpath reportRange reportShouldFail in
                let (_, maps) = check_file include_prelude basedir headers' ds in
                headermap := (path, (headers', maps))::!headermap;
                (headers', maps)
              | Some (headers', maps) ->
                (headers', maps)
            in
            let (maps0, headers_included) = merge_header_maps include_prelude maps0 headers_included headers' in
            merge_header_maps include_prelude (merge_maps l maps maps0) (path::headers_included) headers
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
          if List.mem path headers_included then
            merge_header_maps include_prelude maps0 headers_included headers
          else
          if Filename.check_suffix path ".javaspec" then (* javaspec files van andere jar's*)
            begin
            merge_header_maps include_prelude maps0 (path::headers_included) headers
            end
          else (* laatste el v lijst v headers is path naar jarspec van eigen jar*)
          begin
            let headers_included = path::headers_included in
            let (jarspecs,allspecs)= parse_jarspec_file basedir relpath reportRange in
            let allspecs= remove (fun x -> List.mem x headers_included)(list_remove_dups allspecs) in
            let (classes,lemmas)=extract_specs ((List.map (fun x -> (parse_java_file (Filename.concat basedir x) reportRange)) jarspecs))in
            let (headers',ds) = ([],(List.map (fun x -> (parse_java_file (Filename.concat basedir x) reportRange)) allspecs)) in
            let (_, maps) = check_file include_prelude basedir [] ds in
            headermap := (path, (headers', maps))::!headermap;
            spec_classes:=classes;
            spec_lemmas:=lemmas;
            (merge_maps l maps maps0, headers_included)
          end
        end
    in

    let maps0 = ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []) in
    
    let (maps0, headers_included) =
      if include_prelude then
        if file_type path =Java then
        begin
        match try_assoc rtpath !headermap with
          None -> 
            let (_,allspecs)= parse_jarspec_file rtdir "rt.jarspec" reportRange in
            let ds = (List.map (fun x -> (parse_java_file (Filename.concat rtdir x) reportRange)) allspecs) in
            let (_, maps0) = check_file false bindir [] ds in
            headermap := (rtpath, ([], maps0))::!headermap;
            (maps0, [])
        | Some ([], maps0) ->
          (maps0, [])
        end
        else
        merge_header_maps false maps0 [] [(dummy_loc, "prelude.h")]
      else
        (maps0, [])
    in

    let (maps, _) = merge_header_maps include_prelude maps0 headers_included headers in
    maps
  in

  (* Region: structdeclmap, enumdeclmap, inductivedeclmap *)
  
  let unloadable =
    match language with
      CLang -> let [PackageDecl (_, _, _, ds)] = ps in List.exists (function (UnloadableModuleDecl l) -> true | _ -> false) ds
    | _ -> false
  in
  
  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds_opt)::ds ->
        begin
          match try_assoc sn structmap0 with
            Some (_, Some _, _) -> static_error l "Duplicate struct name."
          | Some (_, None, _) | None -> ()
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
  
  let enumdeclmap = 
    let rec iter edm ds = 
      match ds with
        [] -> edm
      | EnumDecl(l, en, elems) :: ds ->
        begin 
          match try_assoc en edm with
        | Some((l', elems')) -> static_error l "Duplicate enum name."
        | None -> iter ((en, (l, elems)) :: edm) ds
        end
      | _ :: ds -> iter edm ds
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
    flatmap (function (FuncTypeDecl (l, gh, _, g, ftps, _, _)) -> [g, (l, gh, ftps)] | _ -> []) ds
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
   
  (* Region: Java name resolution functions *)
  
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
  
  let resolve (pn, imports) l name map =
    match try_assoc0 name map with
      Some xy as result -> result
    | None ->
      if String.contains name '.' then
        None
      else
        match if pn = "" then None else try_assoc0 (pn ^ "." ^ name) map with
          Some xy as result -> result
        | None ->
          let matches =
            flatmap
              begin function
                Import (l, p, None) ->
                begin match try_assoc0 (p ^ "." ^ name) map with None -> [] | Some xy -> [xy] end
              | Import (l, p, Some name') when name = name' ->
                begin match try_assoc0 (p ^ "." ^ name) map with None -> [] | Some xy -> [xy] end
              | _ -> []
              end
              imports
          in
          match matches with
            [] -> None
          | [xy] -> Some xy
          | _ ->
            let fqns = List.map (fun (x, y) -> "'" ^ x ^ "'") matches in
            static_error l ("Ambiguous imports for name '" ^ name ^ "': " ^ String.concat ", " fqns ^ ".")
  in
  
  let search2' x (pn,imports) xys1 xys2 =
    match search' x (pn,imports) xys1 with
      None -> search' x (pn,imports) xys2
    | result -> result
  in
  
  (* Region: interfdeclmap, classdeclmap *)
  
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
  
  (* Region: check_pure_type: checks validity of type expressions *)
  
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
                    if List.mem_assoc id functypenames || List.mem_assoc id functypemap0 then
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
    | PredTypeExpr (l, tes) -> PredType ([], List.map (check_pure_type (pn,ilist) tpenv) tes )
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
    | PredType ([], pts) -> PredType ([], List.map (instantiate_type tpenv) pts)
    | InferredType t ->
      begin match !t with
        None -> assert false
      | Some t -> instantiate_type tpenv t
      end
    | _ -> t
  in
  
  let instantiate_types tpenv ts =
    if tpenv = [] then ts else List.map (instantiate_type tpenv) ts
  in
  
  let classterms =
    let terms_of xys = List.map (fun (x, _) -> (x, ctxt#mk_app (mk_symbol x [] ctxt#type_int Uninterp) [])) xys in
    terms_of classdeclmap @ terms_of classmap0
  in
  
  (* Region: structmap1 *)
  
  let structmap1 =
    List.map
      (fun (sn, (l, fds_opt)) ->
         let rec iter fmap fds has_ghost_fields =
           match fds with
             [] ->
             (sn,
              (l,
               Some (List.rev fmap),
               if has_ghost_fields then
                 None
               else
                 Some (get_unique_var_symb ("struct_" ^ sn ^ "_padding") (PredType ([], [PtrType (StructType sn)])))
              )
             )
           | Field (lf, gh, t, f,Instance,Public)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name."
             else
               iter ((f, (lf, gh, check_pure_type ("", []) [] t))::fmap) fds (has_ghost_fields || gh = Ghost)
         in
         begin
           match fds_opt with
             Some fds -> iter [] fds false
           | None -> (sn, (l, None, None))
         end
      )
      structdeclmap
  in
  
  let globaldeclmap =
    let rec iter gdm ds =
      match ds with
        [] -> gdm
      | Global(l, te, x, None) :: ds-> (* typecheck the rhs *)
        begin
          match try_assoc x globalmap0 with
            Some(_) -> static_error l "Duplicate global variable name."
          | None -> ()
        end;
        begin
          match try_assoc x gdm with
            Some (_) -> static_error l "Duplicate global variable name."
          | None -> 
            let tp = check_pure_type ("",[]) [] te in
            let global_symb = get_unique_var_symb x tp in
            iter ((x, (l, tp, global_symb)) :: gdm) ds
        end
      | _::ds -> iter gdm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  in
  
  let structmap = structmap1 @ structmap0 in
  
  let enummap1 = enumdeclmap in
  
  let enummap = enummap1 @ enummap0 in
  
  let globalmap1 = globaldeclmap in
  let globalmap = globalmap1 @ globalmap0 in
  
  let isfuncs = if file_type path=Java then [] else
    flatmap (fun (ftn, (_, gh, ftps)) ->
      match (gh, ftps) with
        (Real, []) ->
        let isfuncname = "is_" ^ ftn in
        let domain = [ctxt#type_int] in
        let symb = mk_symbol isfuncname domain ctxt#type_bool Uninterp in
        [(isfuncname, (dummy_loc, [], Bool, [PtrType Void], symb))]
      | _ -> []
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

  (* Region: type compatibility checker *)
  
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
  
  let rec unify t1 t2 =
    t1 == t2 ||
    match (unfold_inferred_type t1, unfold_inferred_type t2) with
      (InferredType t', InferredType t0') -> if t' = t0' then true else begin t0' := Some t1; true end
    | (t, InferredType t0) -> t0 := Some t; true
    | (InferredType t, t0) -> t := Some t0; true
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
      i1=i2 && List.for_all2 unify args1 args2
    | (PtrType t1, PtrType t2) -> compatible_pointees t1 t2
    | (t1, t2) -> t1 = t2
  in
  
  let rec expect_type_core (pn,ilist) l msg t t0 =
    match (unfold_inferred_type t, unfold_inferred_type t0) with
      (ObjType "null", ObjType _) -> ()
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
    | (PredType ([], ts), PredType ([], ts0)) ->
      begin
        match zip ts ts0 with
          None -> static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
        | Some tpairs ->
          List.iter (fun (t, t0) -> expect_type_core (pn,ilist) l msg t t0) tpairs
      end
    | (InductiveType _, AnyType) -> ()
    | _ -> if unify t t0 then () else static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".")
  in
  
  let expect_type (pn,ilist) l t t0 = expect_type_core (pn,ilist) l "" t t0 in
  
  let convert_provertype_expr e proverType proverType0 =
    if proverType = proverType0 then e else ProverTypeConversion (proverType, proverType0, e)
  in
  
  let box e t t0 =
    match unfold_inferred_type t0 with TypeParam _ -> convert_provertype_expr e (provertype_of_type t) ProverInductive | _ -> e
  in
  
  let unbox e t0 t =
    match unfold_inferred_type t0 with TypeParam _ -> convert_provertype_expr e ProverInductive (provertype_of_type t) | _ -> e
  in
  
  (* Region: type-checking of inductive datatypes and fixpoint functions *)
  
  let check_tparams l tparams0 tparams =
    let rec iter tparams =
      match tparams with
        [] -> ()
      | x::xs ->
        if List.mem x tparams0 then static_error l (Printf.sprintf "Type parameter '%s' hides existing type parameter '%s'." x x);
        if List.mem x xs then static_error l (Printf.sprintf "Duplicate type parameter '%s'." x);
        iter xs
    in
    iter tparams
  in
  
  let (inductivemap1, purefuncmap1, fixpointmap1) =
    let rec iter (pn,ilist) imap pfm fpm ds =
      match ds with
        [] -> (List.rev imap, List.rev pfm, List.rev fpm)
      | Inductive (l, i, tparams, ctors)::ds -> let i=full_name pn i in
        check_tparams l [] tparams;
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
        check_tparams l [] tparams;
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
        begin match body_opt with
          Some ([SwitchStmt (ls, e, cs)], _) ->
          let (index, ctorcount, ls, w, wcs) = 
            let ctorcount = List.length cs in
            match e with
              Var (lx, x, _) ->
              begin match try_assoc_i x pmap with
                None -> static_error lx "Fixpoint function must switch on a parameter."
              | Some (index, InductiveType (i, targs)) -> (
                match try_assoc2' (pn,ilist) i imap inductivemap0 with
                  None -> static_error ls "Switch statement cannot precede inductive declaration."
                | Some (_, inductive_tparams, ctormap) ->
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
                          | Operation (l, ((Add | Sub | Mul) as operator), [e1; e2], ts) ->
                            let (w1, w2, t) = promote l e1 e2 ts in
                            begin match t with PtrType _ -> static_error l "This operation is not supported on pointers." | _ -> () end;
                            (Operation (l, operator, [w1; w2], ts), t)
                          | Operation (l, Div, [e1; e2], ts) ->
                            let w1 = checkt e1 RealType in
                            let w2 = checkt e2 RealType in
                            (Operation (l, Div, [w1; w2], ts), RealType)
                          | IntLit (l, n, t) -> if !t = None then t := Some intt; (e, intt)
                          | StringLit (l, s) ->
                            begin match file_type path with
                              Java-> (e, ObjType "java.lang.String")
                            | _ -> (e, PtrType Char)
                            end
                          | CallExpr (l', g', targes, [], pats, info) -> (
                            match (match try_assoc' (pn,ilist) g' pfm with
                              None -> try_assoc' (pn,ilist) g' purefuncmap0
                            | result -> result)
                            with
                              Some (l, callee_tparams, t0, ts0, _) -> (
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
                                static_error l' ("No such pure function: " ^ g')
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
                                        | Some t0 -> tref := Some (t, tenv, targs, t0); (SwitchExpr (l, w, List.rev wcs, tref), t0)
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
              end
            | _ -> static_error l "Fixpoint function must switch on a parameter."
          in
          let fsym = mk_symbol g (List.map (fun (p, t) -> typenode_of_type t) pmap) (typenode_of_type rt) (Proverapi.Fixpoint index) in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, rt, pmap, ls, w, wcs,pn,ilist))::fpm) ds
        | None ->
          let fsym = mk_symbol g (List.map (fun (p, t) -> typenode_of_type t) pmap) (typenode_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) fpm ds
        | _ -> static_error l "Body of fixpoint function must be switch statement."
        end
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
  
  let functypedeclmap1 =
    let rec iter functypedeclmap1 ds =
      match ds with
        [] -> List.rev functypedeclmap1
      | FuncTypeDecl (l, gh, rt, ftn, ftxs, xs, (pre, post))::ds ->
        let (pn,ilist) = ("",[]) in
        if gh = Ghost && ftxs <> [] then static_error l "Parameterized lemma function types are not supported.";
        let _ = if List.mem_assoc ftn functypedeclmap1 || List.mem_assoc ftn functypemap0 then static_error l "Duplicate function type name." in
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
        let ftxmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate function type parameter name.";
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::xm) xs
          in
          iter [] ftxs
        in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm || List.mem_assoc x ftxmap then static_error l "Duplicate parameter name.";
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        iter ((ftn, (l, gh, rt, ftxmap, xmap, pre, post))::functypedeclmap1) ds
      | _::ds -> iter functypedeclmap1 ds
    in
    if file_type path=Java then [] else
    (match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    )
  in
  
  (* Region: predicate families *)
  
  let mk_predfam p l tparams arity ts inputParamCount = (p, (l, tparams, arity, ts, get_unique_var_symb p (PredType (tparams, ts)), inputParamCount)) in

  let struct_padding_predfams1 =
    flatmap
      (function
         (sn, (l, fds, Some padding_predsymb)) -> [("struct_" ^ sn ^ "_padding", (l, [], 0, [PtrType (StructType sn)], padding_predsymb, Some 1))]
       | _ -> [])
      structmap1
  in
  
  let is_lemmafunctype_pred_map1 =
    flatmap
      (function
         (g, (l, Ghost, _)) ->
         [(g, mk_predfam ("is_" ^ g) l [] 0 [PtrType (FuncType g)] None)]
       | _ -> []
      )
      functypenames
  in
  
  let islemmafunctypepreds1 = List.map (fun (_, p) -> p) is_lemmafunctype_pred_map1 in
  
  let is_paramizedfunctype_pred_map1 =
    flatmap
      begin function
        (g, (l, Real, rt, ftxmap, xmap, pre, post)) when ftxmap <> [] ->
        let paramtypes = [PtrType (FuncType g)] @ List.map snd ftxmap in
        [(g, mk_predfam ("is_" ^ g) l [] 0 paramtypes (Some (List.length paramtypes)))]
      | _ -> []
      end
      functypedeclmap1
  in
  
  let isparamizedfunctypepreds1 = List.map snd is_paramizedfunctype_pred_map1 in
  
  let malloc_block_pred_map1 = 
    match file_type path with
    Java-> []
    | _ -> flatmap (function (sn, (l, Some _, _)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) l [] 0 
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
              ((cn, fn), mk_predfam (cn ^ "_" ^ fn) l [] 0 [ObjType cn; t] (Some 1))
             )
             fds
      )
      classfmap
    | _ ->
    flatmap
      (fun (sn, (_, fds_opt, _)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (l, gh, t)) ->
              ((sn, fn), mk_predfam (sn ^ "_" ^ fn) l [] 0 [PtrType (StructType sn); t] (Some 1))
             )
             fds
      )
      structmap1
  in
  
  let field_pred_map = field_pred_map1 @ field_pred_map0 in
  
  let structpreds1 = List.map (fun (_, p) -> p) malloc_block_pred_map1 @ List.map (fun (_, p) -> p) field_pred_map1 @ struct_padding_predfams1 in
  
  let predfammap1 =
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyDecl (l, p, tparams, arity, tes, inputParamCount)::ds -> let p=full_name pn p in
        let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
        begin
          match try_assoc2' (pn,ilist) p pm predfammap0 with
            Some (l0, tparams0, arity0, ts0, symb0, inputParamCount0) ->
            let tpenv =
              match zip tparams0 (List.map (fun x -> TypeParam x) tparams) with
                None -> static_error l "Predicate family redeclarations declares a different number of type parameters."
              | Some bs -> bs
            in
            let ts0' = List.map (instantiate_type tpenv) ts0 in
            if arity <> arity0 || ts <> ts0' || inputParamCount <> inputParamCount0 then
              static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.");
            iter (pn,ilist) pm ds
          | None ->
            iter (pn,ilist) (mk_predfam p l tparams arity ts inputParamCount::pm) ds
        end
      | _::ds -> iter (pn,ilist) pm ds
      | [] -> List.rev pm
    in
    let rec iter' pm ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter (pn,il) pm ds) rest
      | [] -> pm
    in
    iter' (islemmafunctypepreds1 @ isparamizedfunctypepreds1 @ structpreds1) ps
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
        let pfm = mk_predfam bcn l [] 0 (BoxIdType::List.map (fun (x, t) -> t) boxpmap) (Some 1)::pfm in
        let pfm = mk_predfam default_hpn l [] 0 (HandleIdType::BoxIdType::[]) (Some 1)::pfm in
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
              iter (mk_predfam hpn l [] 0 (HandleIdType::BoxIdType::List.map (fun (x, t) -> t) pmap) (Some 1)::pfm) ((hpn, (l, pmap, inv, pbcs))::hpm) hpds
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
  
  let predfammap = predfammap1 @ predfammap0 in (* TODO: Check for name clashes here. *)
  
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
        let pf = (p, (l, [], PredType ([], List.map (fun (x, t) -> t) ps2), List.map (fun (x, t) -> t) ps1, funcsym)) in
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
  
  (* Region: The type checker *)
  
  let funcnames = if file_type path=Java then [] else
  let ds= (match ps with[PackageDecl(_,"",[],ds)] ->ds) in
  list_remove_dups (flatmap (function (Func (l, (Regular|Lemma), tparams, rt, g, ps, atomic, ft, c, b,Static,Public)) -> [g] | _ -> []) ds) 
  in
  
  let check_classname (pn, ilist) (l, c) =
    match search2' c (pn, ilist) classdeclmap classmap0 with 
      None -> static_error l "No such class name."
    | Some s -> s
  in
  
  let check_classnamelist (pn,ilist) is =
    List.map (check_classname (pn, ilist)) is
  in
  
  let check_funcnamelist is =
    List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such function name."; i) is 
  in
  
  let rec check_expr (pn,ilist) tparams tenv e =
    let check e = check_expr (pn,ilist) tparams tenv e in
    let checkt e t0 = check_expr_t_core (pn,ilist) tparams tenv e t0 false in
    let checkt_cast e t0 = check_expr_t_core (pn,ilist) tparams tenv e t0 true in
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
      | Some t -> scope := Some LocalVar; (e, t)
      | None ->
      match try_assoc' (pn,ilist) x purefuncmap with
      | Some (_, tparams, t, [], _) ->
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
      if List.mem x funcnames then
        match file_type path with
          Java -> static_error l "In java methods can't be used as pointers"
        | _ -> scope := Some FuncName; (e, PtrType Void)
      else
      match try_assoc' (pn,ilist) x predfammap with
      | Some (_, tparams, arity, ts, _, _) ->
        if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
        if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported.";
        scope := Some PredFamName;
        (e, PredType (tparams, ts))
      | None ->
      let enumElems = flatmap (fun (name, (l, elems)) -> imap (fun i x -> (x, i)) elems) enummap in
      match try_assoc x enumElems with
      | Some i ->
        scope := Some (EnumElemName i);
        (e, IntType)
      | None ->
      match try_assoc' (pn, ilist) x globalmap with
      | Some ((l, tp, symbol)) -> scope := Some GlobalName; (e, tp)
      | None ->
      match try_assoc x modulemap with
      | Some _ -> scope := Some ModuleName; (e, IntType)
      | None ->
      static_error l ("No such variable, constructor, regular function, predicate, enum element, global variable, or module: " ^ x)
      end
    | PredNameExpr (l, g) ->
      begin
        match try_assoc' (pn,ilist) g predfammap with
          Some (_, tparams, arity, ts, _, _) ->
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported.";
          if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported.";
          (e, PredType (tparams, ts))
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
    | Operation (l, (BitAnd | BitXor | BitOr as operator), [e1; e2], ts) ->
      let w1 = checkt e1 UintPtrType in
      let w2 = checkt e2 UintPtrType in
      (Operation (l, operator, [w1; w2], ts), UintPtrType)
    | Operation (l, BitNot, [e], ts) ->
      let w = checkt e UintPtrType in
      (Operation (l, BitNot, [w], ts), UintPtrType)
    | Operation (l, (Le | Lt as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote l e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt)
    | Operation (l, (Add | Sub as operator), [e1; e2], ts) ->
      let (w1, t1) = check e1 in
      let (w2, t2) = check e2 in
      begin
        match t1 with
          PtrType pt1 ->
          begin match t2 with
            PtrType pt2 when operator = Sub ->
            if pt1 <> pt2 then static_error l "Pointers must be of same type";
            if pt1 <> Char && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported";
            ts:=Some [t1; t2];
            (Operation (l, operator, [w1; w2], ts), IntType)
          | _ ->
            let w2 = checkt e2 intt in
            ts:=Some [t1; IntType];
            (Operation (l, operator, [w1; w2], ts), t1)
          end
        | IntType | RealType ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (Operation (l, operator, [w1; w2], ts), t)
        | ObjType "java.lang.String" as t when operator = Add ->
          let w2 = checkt e2 t in
          ts:=Some [t1; ObjType "java.lang.String"];
          (Operation (l, operator, [w1; w2], ts), t1)
        | _ -> static_error l ("Operand of addition or subtraction must be pointer, integer, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2))
      end
    | Operation (l, Mul, [e1; e2], ts) ->
      let (w1, w2, t) = promote l e1 e2 ts in
      begin match t with PtrType _ -> static_error l "Cannot multiply pointers." | _ -> () end;
      (Operation (l, Mul, [w1; w2], ts), t)
    | Operation (l, Div, [e1; e2], ts) ->
      let w1 = checkt e1 RealType in
      let w2 = checkt e2 RealType in
      (Operation (l, Div, [w1; w2], ts), RealType)
    | IntLit (l, n, t) -> (e, match !t with None -> t := Some intt; intt | Some t -> t)
    | ClassLit (l, s) ->
      let s = check_classname (pn, ilist) (l, s) in
      (ClassLit (l, s), ObjType "Class")
    | StringLit (l, s) -> (match file_type path with
        Java-> (e, ObjType "java.lang.String")
      | _ -> (e, PtrType Char))
    | CastExpr (l, te, e) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let w = checkt_cast e t in
      (CastExpr (l, ManifestTypeExpr (type_expr_loc te, t), w), t)
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
                  | Some t0 -> tref := Some (t, tenv, targs, t0); (SwitchExpr (l, w, wcs, tref), t0)
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
    | SizeofExpr(l, te) ->
      let t = check_pure_type (pn,ilist) tparams te in
      (e, IntType)
    | e -> static_error (expr_loc e) "Expression form not allowed here."
  and check_expr_t (pn,ilist) tparams tenv e t0 = check_expr_t_core (pn, ilist) tparams tenv e t0 false
  and check_expr_t_core (pn,ilist) tparams tenv e t0 isCast =
    match (e, t0) with
      (IntLit (l, n, t), PtrType _) when isCast || eq_big_int n zero_big_int -> t:=Some t0; e
    | (IntLit (l, n, t), UintPtrType) -> t:=Some UintPtrType; e
    | (IntLit (l, n, t), RealType) -> t:=Some RealType; e
    | (IntLit (l, n, t), Char) ->
      t:=Some Char;
      if not (le_big_int (big_int_of_int (-128)) n && le_big_int n (big_int_of_int 127)) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
          let n = if 128 <= n then n - 256 else n in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as char must be between -128 and 127."
      else
        e
    | _ ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      match (t, t0) with
        (ObjType _, ObjType _) when isCast -> w
      | (PtrType _, UintPtrType) when isCast -> w
      | (UintPtrType, PtrType _) when isCast -> w
      | (IntType, Char) when isCast -> w
      | _ -> expect_type (pn,ilist) (expr_loc e) t t0; w
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
        (_, Some fds, _) ->
        begin
          match try_assoc' (pn,ilist) f#name fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.")
          | Some (_, gh, t) -> check_ok gh; f#set_parent sn; f#set_range t; (w, t)
        end
      | (_, None, _) -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' was declared without a body.")
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

  (* Region: type checking of assertions *)
  
  let check_pat_core (pn,ilist) l tparams tenv t p =
    match p with
      LitPat e -> let w = check_expr_t (pn,ilist) tparams tenv e t in (LitPat w, [])
    | VarPat x ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
      (p, [(x, t)])
    | DummyPat -> (p, [])
  in
  
  let check_pat (pn,ilist) l tparams tenv t p = let (w, tenv') = check_pat_core (pn,ilist) l tparams tenv t p in (w, tenv' @ tenv) in

  let merge_tenvs l tenv1 tenv2 =
    let rec iter tenv1 tenv3 =
      match tenv1 with
        [] -> tenv3
      | ((x, t) as xt)::tenv1 ->
        if List.mem_assoc x tenv2 then static_error l (Printf.sprintf "Variable name clash: '%s'" x);
        iter tenv1 (xt::tenv3)
    in
    iter tenv1 tenv2
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

  let rec check_pred_core (pn,ilist) tparams tenv p =
    let check_pred = check_pred_core in
    match p with
      Access (l, e, f, v) ->
      let (w, t) = check_deref false true (pn,ilist) l tparams tenv e f in
      let (wv, tenv') = check_pat (pn,ilist) l tparams tenv t v in
      (Access (l, w, f, wv), tenv', [])
    | CallPred (l, p, targs, ps0, ps) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (p, callee_tparams, arity, xs, inputParamCount) =
        match resolve (pn,ilist) l p#name predfammap with
          Some (pname, (_, callee_tparams, arity, xs, _, inputParamCount)) -> (new predref pname, callee_tparams, arity, xs, inputParamCount)
        | None ->
          begin
            match try_assoc p#name tenv with
              None -> static_error l ("No such predicate: " ^ p#name)
            | Some (PredType (callee_tparams, ts)) -> (new predref (p#name), callee_tparams, 0, ts, None)
            | Some _ -> static_error l ("Variable is not of predicate type: " ^ p#name)
          end
      in
      begin
        let (targs, tpenv, inferredTypes) =
          if targs = [] then
            let tpenv = List.map (fun x -> (x, ref None)) callee_tparams in
            (List.map (fun (x, r) -> InferredType r) tpenv,
             List.map (fun (x, r) -> (x, InferredType r)) tpenv,
             List.map (fun (x, r) -> r) tpenv)
          else
            match zip callee_tparams targs with
              None -> static_error l (Printf.sprintf "Predicate requires %d type arguments." (List.length callee_tparams))
            | Some bs -> (targs, bs, [])
        in
        if List.length ps0 <> arity then static_error l "Incorrect number of indexes.";
        let ts0 = match file_type path with
          Java-> list_make arity (ObjType "Class")
        | _   -> list_make arity (PtrType Void)
        in
        let (wps0, tenv) = check_pats (pn,ilist) l tparams tenv ts0 ps0 in
        let xs' = List.map (instantiate_type tpenv) xs in
        let (wps, tenv) = check_pats (pn,ilist) l tparams tenv xs' ps in
        p#set_domain (ts0 @ xs'); p#set_inputParamCount inputParamCount;
        (WCallPred (l, p, targs, wps0, wps), tenv, inferredTypes)
      end
    | ExprPred (l, e) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in (ExprPred (l, w), tenv, [])
    | Sep (l, p1, p2) ->
      let (p1, tenv, infTps1) = check_pred (pn,ilist) tparams tenv p1 in
      let (p2, tenv, infTps2) = check_pred (pn,ilist) tparams tenv p2 in
      (Sep (l, p1, p2), tenv, infTps1 @ infTps2)
    | IfPred (l, e, p1, p2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let (wp1, _, infTps1) = check_pred (pn,ilist) tparams tenv p1 in
      let (wp2, _, infTps2) = check_pred (pn,ilist) tparams tenv p2 in
      (IfPred (l, w, wp1, wp2), tenv, infTps1 @ infTps2)
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
          let rec iter wcs ctormap cs infTps =
            match cs with
              [] ->
              let _ = 
                match ctormap with
                  [] -> ()
                | (cn, _)::_ ->
                  static_error l ("Missing case: '" ^ cn ^ "'.")
              in (SwitchPred (l, w, wcs), tenv, infTps)
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
                      let xInfo = match unfold_inferred_type t with TypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None in
                      iter ((x, instantiate_type tpenv t)::xmap) (xInfo::xsInfo) ts xs
                    | ([], _) -> static_error lc "Too many pattern variables."
                    | _ -> static_error lc "Too few pattern variables."
                  in
                  iter [] [] ts xs
                in
                ref_xsInfo := Some xsInfo;
                let tenv = xmap @ tenv in
                let (wbody, _, clauseInfTps) = check_pred (pn,ilist)  tparams tenv body in
                let Some cn = search' cn (pn,ilist) ctormap in
                iter (SwitchPredClause (lc, cn, xs, ref_xsInfo, wbody)::wcs) (List.remove_assoc cn ctormap) cs (clauseInfTps @ infTps)
              end
          in
          iter [] ctormap cs []
        end
      | _ -> static_error l "Switch operand is not an inductive value."
      end
    | EmpPred l -> (p, tenv, [])
    | CoefPred (l, coef, body) ->
      let (wcoef, tenv') = check_pat_core (pn,ilist) l tparams tenv RealType coef in
      let (wbody, tenv, infTps) = check_pred (pn,ilist) tparams tenv body in
      (CoefPred (l, wcoef, wbody), merge_tenvs l tenv' tenv, infTps)
  in
  
  let rec fix_inferred_type r =
    match !r with
      None -> r := Some Bool (* any type will do *)
    | Some (InferredType r) -> fix_inferred_type r
    | _ -> ()
  in
  
  let fix_inferred_types rs = List.map fix_inferred_type rs in
  
  let check_pred (pn,ilist) tparams tenv p =
    let (wpred, tenv, infTypes) = check_pred_core (pn,ilist) tparams tenv p in
    fix_inferred_types infTypes;
    (wpred, tenv)
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
  
  (* Region: predicate preciseness check *)
  
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
    | CastExpr (_, _, e) -> vars_used e
    | SizeofExpr (_, _) -> []
    | ProverTypeConversion (_, _, e) -> vars_used e
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
    | WCallPred (l, g, targs, pats0, pats) ->
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
  
  (* Region: Predicate instances *)
  
  let predinstmap1 =
    flatmap
      begin
        function
          (sn, (_, Some fmap, _)) ->
          flatmap
            begin
              function
                (f, (l, Real, t)) ->
                begin
                let predinst p =
                  p#set_inputParamCount (Some 1);
                  ((sn ^ "_" ^ f, []),
                   ([], l, [], [sn, PtrType (StructType sn); "value", t], Some 1,
                    (let fref = new fieldref f in
                    fref#set_parent sn;
                    fref#set_range t;
                    WCallPred (l, p, [], [], [LitPat (AddressOf (l, Read (l, Var (l, sn, ref (Some LocalVar)), fref))); LitPat (Var (l, "value", ref (Some LocalVar)))]))
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
  
  let check_predinst (pn, ilist) tparams tenv env l p predinst_tparams fns xs body =
    let (p, predfam_tparams, arity, ps, inputParamCount) =
      match resolve (pn,ilist) l p predfammap with
        None -> static_error l ("No such predicate family: "^p)
      | Some (p, (_, predfam_tparams, arity, ps, _, inputParamCount)) -> (p, predfam_tparams, arity, ps, inputParamCount)
    in
    check_tparams l tparams predinst_tparams;
    let tpenv =
      match zip predfam_tparams (List.map (fun x -> TypeParam x) predinst_tparams) with
        None -> static_error l "Number of type parameters does not match predicate family."
      | Some bs -> bs
    in
    if List.length fns <> arity then static_error l "Incorrect number of indexes.";
    let pxs =
      match zip ps xs with
        None -> static_error l "Incorrect number of parameters."
      | Some pxs -> pxs
    in
    let tparams' = predinst_tparams @ tparams in
    let xs =
      let rec iter2 xm pxs =
        match pxs with
          [] -> List.rev xm
        | (t0, (te, x))::xs -> 
          let t = check_pure_type (pn,ilist) tparams' te in
          expect_type (pn,ilist) l t (instantiate_type tpenv t0);
          if List.mem_assoc x tenv then static_error l ("Parameter '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.");
          if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
          iter2 ((x, t)::xm) xs
      in
      iter2 [] pxs
    in
    let (wbody, _) = check_pred (pn,ilist) tparams' (xs @ tenv) body in
    begin
      match inputParamCount with
        None -> ()
      | Some n ->
        let (inps, outps) = take_drop n (List.map (fun (x, t) -> x) xs) in
        let inps = inps @ List.map (fun (x, t) -> x) tenv in
        let fixed = check_pred_precise inps wbody in
        List.iter
          (fun x ->
           if not (List.mem x fixed) then
             static_error l ("Preciseness check failure: body does not fix output parameter '" ^ x ^ "'."))
          outps
    end;
    ((p, fns), (env, l, predinst_tparams, xs, inputParamCount, wbody))
  in
  
  let predinstmap1 = 
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyInstanceDecl (l, p, tparams, is, xs, body)::ds ->
        let fns = match file_type path with
          Java-> check_classnamelist (pn,ilist) is
        | _ -> check_funcnamelist is 
        in
        let (pfns, info) as entry = check_predinst (pn, ilist) [] [] [] l p tparams fns xs body in
        let _ = if List.mem_assoc pfns pm || List.mem_assoc pfns predinstmap0 then static_error l "Duplicate predicate family instance." in
        iter (pn,ilist) (entry::pm) ds
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

  (* Region: evaluation helpers; pushing and popping assumptions and execution trace elements *)
  
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
  
  let struct_sizes =
    List.map
      begin fun (sn, _) ->
        let s = get_unique_var_symb ("struct_" ^ sn ^ "_size") IntType in
        ctxt#assume (ctxt#mk_lt (ctxt#mk_intlit 0) s);
        (sn, s)
      end
      structmap
  in
  
  let sizeof l t =
    match t with
      Void | Char -> ctxt#mk_intlit 1
    | IntType -> ctxt#mk_intlit 4
    | PtrType _ -> ctxt#mk_intlit 4
    | StructType sn -> List.assoc sn struct_sizes
    | _ -> static_error l ("Taking the size of type " ^ string_of_type t ^ " is not yet supported.")
  in
  
  let field_offsets =
    flatmap
      begin
        function
          (sn, (_, Some fmap, _)) ->
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
  
  let field_offset l f =
    match try_assoc (f#parent, f#name) field_offsets with
      Some term -> term
    | None -> static_error l "Cannot take the address of a ghost field"
  in
  let field_address l t f = ctxt#mk_add t (field_offset l f) in
  
  let convert_provertype term proverType proverType0 =
    if proverType = proverType0 then term else apply_conversion proverType proverType0 term
  in
  
  let prover_convert_term term t t0 =
    if t = t0 then term else convert_provertype term (provertype_of_type t) (provertype_of_type t0)
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
    stats#proverAssume;
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
         let h' =
           List.map
             begin fun (Chunk ((g, literal), targs, coef, ts, size)) ->
               Chunk ((ctxt#pprint g, literal), targs, ctxt#pprint coef, List.map (fun t -> ctxt#pprint t) ts, size)
             end
             h
         in
         let env' = List.map (fun (x, t) -> (x, ctxt#pprint t)) env in
         Executing (h', env', l, msg)
       | PushSubcontext -> PushSubcontext
       | PopSubcontext -> PopSubcontext)
      cs
  in

  let assert_term t h env l msg =
    stats#proverOtherQuery;
    if not (ctxt#query t) then
      raise (SymbolicExecutionError (pprint_context_stack !contextStack, ctxt#pprint t, l, msg))
  in

  let assert_false h env l msg =
    raise (SymbolicExecutionError (pprint_context_stack !contextStack, "false", l, msg))
  in

  (* Region: evaluation *)
  
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
          LocalVar -> (try List.assoc x env with Not_found -> assert_false [] env l (Printf.sprintf "Unbound variable '%s'" x))
        | PureCtor -> let Some (lg, tparams, t, [], s) = try_assoc' (pn,ilist) x purefuncmap in ctxt#mk_app s []
        | FuncName -> (List.assoc x funcnameterms)
        | PredFamName -> let Some (_, _, _, _, symb, _) = (try_assoc' (pn,ilist) x predfammap)in symb
        | EnumElemName(n) -> ctxt#mk_intlit n
        | GlobalName ->
          begin
            match read_field with
              None -> static_error l "Cannot mention global variables in this context."
            | Some (read_field, deref_pointer) ->
                let Some((_, tp, symbol)) = try_assoc' (pn, ilist) x globalmap in 
                  deref_pointer l symbol tp
          end
        | ModuleName -> List.assoc x modulemap
      end
    | PredNameExpr (l, g) -> let Some (_, _, _, _, symb, _) = (try_assoc' (pn,ilist) g predfammap) in symb
    | CastExpr (l, ManifestTypeExpr (_, t), e) -> 
      begin
        match (e, t) with
          (IntLit (_, n, _), PtrType _) ->
          if assert_term <> None && not (le_big_int zero_big_int n && le_big_int n max_ptr_big_int) then static_error l "Int literal is out of range.";
          ctxt#mk_intlit_of_string (string_of_big_int n)
        | (e, Char) ->
          check_overflow l min_char_term (ev e) max_char_term
        | _ -> ev e
      end
    | IntLit (l, n, t) ->
      begin match !t with
        Some RealType ->
        if eq_big_int n unit_big_int then real_unit
        else ctxt#mk_reallit_of_num (num_of_big_int n)
      | Some t ->
        if assert_term <> None then
        begin
          let (min, max) =
            match t with
              IntType -> (min_int_big_int, max_int_big_int)
            | Char -> (min_char_big_int, max_char_big_int)
            | (UintPtrType|PtrType _) -> (zero_big_int, max_ptr_big_int)
          in
          if not (le_big_int min n && le_big_int n max) then static_error l "Int literal is out of range."
        end;
        try
          let n = int_of_big_int n in ctxt#mk_intlit n
        with Failure "int_of_big_int" -> ctxt#mk_intlit_of_string (string_of_big_int n)
      end
    | ClassLit (l,s) -> List.assoc s classterms
    | StringLit (l, s) -> (match file_type path with
        Java -> get_unique_var_symb "stringLiteral" (ObjType "java.lang.String")
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
    | Operation (l, BitAnd, [e1; Operation (_, BitNot, [e2], ts2)], ts1) ->
      ctxt#mk_app bitwise_and_symbol [ev e1; ctxt#mk_app bitwise_not_symbol [ev e2]]
    | Operation (l, BitNot, _, _) ->
      static_error l "VeriFast does not currently support a bitwise complement (~) expression except as part of a bitwise AND (x & ~y)."
    | Operation (l, (BitAnd|BitXor|BitOr as operator), es, ts) ->
      let symb =
        match operator with
          BitAnd -> bitwise_and_symbol
        | BitXor -> bitwise_xor_symbol
        | BitOr -> bitwise_or_symbol
      in
      ctxt#mk_app symb (List.map ev es)
    | IfExpr (l, e1, e2, e3) -> ctxt#mk_ifthenelse (ev e1) (ev e2) (ev e3)
    | Operation (l, Eq, [e1; e2], ts) ->
      if !ts = Some [Bool; Bool] then
        ctxt#mk_iff (ev e1) (ev e2)
      else
        ctxt#mk_eq (ev e1) (ev e2)
    | Operation (l, Neq, [e1; e2], ts) -> ctxt#mk_not (ctxt#mk_eq (ev e1) (ev e2))
    | Operation (l, Add, [e1; e2], ts) ->
      begin
        match !ts with
          Some [IntType; IntType] ->
          check_overflow l min_int_term (ctxt#mk_add (ev e1) (ev e2)) max_int_term
        | Some [PtrType t; IntType] ->
          let n = sizeof l t in
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_add (ev e1) (ctxt#mk_mul n (ev e2))) max_ptr_term
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
          check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_sub (ev e1) (ctxt#mk_mul n (ev e2))) max_ptr_term
        | Some [RealType; RealType] ->
          ctxt#mk_real_sub (ev e1) (ev e2)
        | Some [PtrType (Char | Void); PtrType (Char | Void)] ->
          check_overflow l min_int_term (ctxt#mk_sub (ev e1) (ev e2)) max_int_term
      end
    | Operation (l, Mul, [e1; e2], ts) ->
      begin match !ts with
        Some [IntType; IntType] ->
        check_overflow l min_int_term (ctxt#mk_mul (ev e1) (ev e2)) max_int_term
      | Some [RealType; RealType] ->
        ctxt#mk_real_mul (ev e1) (ev e2)
      end
    | Operation (l, Div, [e1; e2], ts) ->
      let rec eval_reallit e =
        match e with
          IntLit (l, n, t) -> num_of_big_int n
        | _ -> static_error (expr_loc e) "The denominator of a division must be a literal."
      in
      ctxt#mk_real_mul (ev e1) (ctxt#mk_reallit_of_num (div_num (num_of_int 1) (eval_reallit e2)))
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
          field_address l (ev e) f
        | Var (l, x, scope) when ! scope = Some(GlobalName) ->
            let Some((l, tp, symbol)) = try_assoc' (pn, ilist) x globalmap in  symbol
        | _ -> static_error l "Taking the address of this expression is not supported."
      end
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
      let (Some (tt, tenv, targs, tp)) = !tref in
      let symbol = ctxt#mk_symbol g (typenode_of_type tt :: List.map (fun (x, _) -> typenode_of_type (List.assoc x tenv)) env) (typenode_of_type tp) (Proverapi.Fixpoint 0) in
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
                    match unfold_inferred_type typ with
                      TypeParam x -> (pat, convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv)))
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
    | ProverTypeConversion (tfrom, tto, e) -> convert_provertype (ev e) tfrom tto
    | SizeofExpr (l, te) ->
      let t = check_pure_type (pn,ilist) [] te in
      sizeof l t
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
                     match unfold_inferred_type typ with
                       TypeParam x -> convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv))
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
  
  (* Region: production of assertions *)
  
  let assert_expr (pn,ilist) env e h env l msg = assert_term (eval (pn,ilist) None env e) h env l msg in
  
  let success() = () in
  
  let branch cont1 cont2 =
    stats#branch;
    in_temporary_context (fun _ -> cont1());
    in_temporary_context (fun _ -> cont2())
  in
  
  let evalpat (pn,ilist) ghostenv env pat tp0 tp cont =
    match pat with
      LitPat e -> cont ghostenv env (prover_convert_term (eval (pn,ilist) None env e) tp0 tp)
    | VarPat x -> let t = get_unique_var_symb x tp in cont (x::ghostenv) (update env x (prover_convert_term t tp tp0)) t
    | DummyPat -> let t = get_unique_var_symb "dummy" tp in cont ghostenv env t
  in
  
  let rec evalpats (pn,ilist) ghostenv env pats tps0 tps cont =
    match (pats, tps0, tps) with
      ([], [], []) -> cont ghostenv env []
    | (pat::pats, tp0::tps0, tp::tps) -> evalpat (pn,ilist) ghostenv env pat tp0 tp (fun ghostenv env t -> evalpats (pn,ilist) ghostenv env pats tps0 tps (fun ghostenv env ts -> cont ghostenv env (t::ts)))
  in

  let real_mul l t1 t2 =
    if t1 == real_unit then t2 else if t2 == real_unit then t1 else
    let t = ctxt#mk_real_mul t1 t2 in
    if is_dummy_frac_term t1 || is_dummy_frac_term t2 then dummy_frac_terms := t::!dummy_frac_terms;
    t
  in
  
  let real_div l t1 t2 =
    if t2 == real_unit then t1 else static_error l "Real division not yet supported."
  in
  
  let definitely_equal t1 t2 =
    let result = if t1 == t2 then (stats#definitelyEqualSameTerm; true) else (stats#definitelyEqualQuery; ctxt#query (ctxt#mk_eq t1 t2)) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  in
  
  let predname_eq g1 g2 =
    match (g1, g2) with
      ((g1, literal1), (g2, literal2)) -> if literal1 && literal2 then g1 == g2 else definitely_equal g1 g2
  in
  
  let assume_field h0 f tp tv tcoef cont =
    let (_, (_, _, _, _, symb, _)) =(List.assoc (f#parent, f#name) field_pred_map)in
    begin fun cont ->
      if tcoef != real_unit && tcoef != real_half then
        assume (ctxt#mk_real_lt real_zero tcoef) cont
      else
        cont()
    end $. fun () ->
    let rec iter h =
      match h with
        [] -> cont (Chunk ((symb, true), [], tcoef, [tp; tv], None)::h0)
      | Chunk ((g, true), targs', tcoef', [tp'; tv'], _) as chunk::h when g == symb ->
        if tcoef' == real_unit then
          assume_neq tp tp' (fun _ -> iter h)
        else if definitely_equal tp tp' then
        begin
          assume (ctxt#mk_eq tv tv') $. fun () ->
          let coef =
            if is_dummy_frac_term tcoef then
              tcoef'
            else if is_dummy_frac_term tcoef' then
              tcoef
            else
              ctxt#mk_real_add tcoef tcoef'
          in
          cont (Chunk ((symb, true), [], coef, [tp'; tv'], None)::List.filter (fun ch -> ch != chunk) h0)
        end
        else
          iter h
      | _::h -> iter h
    in
    iter h0
  in
  
  let assume_chunk h g_symb targs coef inputParamCount ts size cont =
    if inputParamCount = None || coef == real_unit then
      cont (Chunk (g_symb, targs, coef, ts, size)::h)
    else
      let Some n = inputParamCount in
      let rec iter hdone htodo =
        match htodo with
          [] -> cont (Chunk (g_symb, targs, coef, ts, size)::h)
        | Chunk (g_symb', targs', coef', ts', size') as chunk::htodo ->
          if predname_eq g_symb g_symb' && List.for_all2 unify targs targs' && for_all_take2 definitely_equal n ts ts' then
            let assume_all_eq ts ts' cont =
              let rec iter ts ts' =
                match (ts, ts') with
                  (t::ts, t'::ts') -> assume (ctxt#mk_eq t t') (fun () -> iter ts ts')
                | ([], []) -> cont ()
              in
              iter ts ts'
            in
            assume_all_eq (drop n ts) (drop n ts') $. fun () ->
            let h = if List.length hdone < List.length htodo then hdone @ htodo else htodo @ hdone in
            let coef =
              if is_dummy_frac_term coef then
                coef'
              else if is_dummy_frac_term coef' then
                coef
              else
                ctxt#mk_real_add coef coef'
            in
            cont (Chunk (g_symb, targs, coef, ts, size)::h)
          else
            iter (chunk::hdone) htodo
      in
      iter [] h
  in

  let rec assume_pred tpenv (pn,ilist) h ghostenv (env: (string * 'termnode) list) p coef size_first size_all cont =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ -> with_context (Executing (h, env, pred_loc p, "Producing assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval (pn,ilist) None env in
    match p with
    | Access (l, e, f, rhs) ->
      let te = ev e in
      evalpat (pn,ilist) ghostenv env rhs f#range f#range (fun ghostenv env t -> assume_field h f te t coef (fun h -> cont h ghostenv env))
    | WCallPred (l, g, targs, pats0, pats) ->
      let g_symb =
        match try_assoc g#name predfammap with
          Some (_, _, _, _, symb, _) -> (symb, true)
        | None -> (List.assoc g#name env, false)
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv g#domain in
      evalpats (pn,ilist) ghostenv env (pats0 @ pats) g#domain domain (fun ghostenv env ts ->
        assume_chunk h g_symb targs coef g#inputParamCount ts size_first (fun h -> cont h ghostenv env)
      )
    | ExprPred (l, e) -> assume (ev e) (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) -> assume_pred tpenv (pn,ilist) h ghostenv env p1 coef size_first size_all (fun h ghostenv env -> assume_pred tpenv (pn,ilist) h ghostenv env p2 coef size_all size_all cont)
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ = cont h ghostenv env in
      branch
        (fun _ -> assume (ev e) (fun _ -> assume_pred tpenv (pn,ilist) h ghostenv env p1 coef size_all size_all cont))
        (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> assume_pred tpenv (pn,ilist) h ghostenv env p2 coef size_all size_all cont))
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
                        let term' = convert_provertype term proverType ProverInductive in
                        (x, term', term)
                     )
                     pts
               in
               let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
               assume_eq t (ctxt#mk_app cs (List.map (fun (x, t, _) -> t) xts)) (fun _ -> assume_pred tpenv (pn,ilist) h (pats @ ghostenv) (xenv @ env) p coef size_all size_all cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env
    | CoefPred (l, DummyPat, body) ->
      assume_pred tpenv (pn,ilist) h ghostenv env body (get_dummy_frac_term ()) size_first size_all cont
    | CoefPred (l, coef', body) ->
      evalpat (pn,ilist) ghostenv env coef' RealType RealType $. fun ghostenv env coef' ->
      assume_pred tpenv (pn,ilist) h ghostenv env body (real_mul l coef coef') size_first size_all cont
    )
  in
  
  (* Region: consumption of assertions *)
  
  (* env' contains the bindings of unbound variables, as when closing a predicate chunk without specifying all arguments *)
  let match_chunk (pn,ilist) ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps (Chunk (g', targs0, coef0, ts0, size0)) =
    let match_pat ghostenv env env' isInputParam pat tp0 tp t cont =
      let match_terms v t =
        if definitely_equal v t then
          cont ghostenv env env'
        else if isInputParam then
          None
        else
          assert_false h env l (Printf.sprintf "Cannot prove %s == %s" (ctxt#pprint t) (ctxt#pprint v))
      in
      match (pat, t) with
      | (SrcPat (LitPat (Var (lx, x, scope))), t) when !scope = Some LocalVar ->
        begin match try_assoc x env with
          Some t' -> match_terms (prover_convert_term t' tp0 tp) t
        | None -> let binding = (x, prover_convert_term t tp tp0) in cont ghostenv (binding::env) (binding::env')
        end
      | (SrcPat (LitPat e), t) ->
        match_terms (prover_convert_term (eval (pn,ilist) None env e) tp0 tp) t
      | (TermPat t0, t) -> match_terms (prover_convert_term t0 tp0 tp) t
      | (SrcPat (VarPat x), t) -> cont (x::ghostenv) ((x, prover_convert_term t tp tp0)::env) env'
      | (SrcPat DummyPat, t) -> cont ghostenv env env'
    in
    let rec match_pats ghostenv env env' index pats tps0 tps ts cont =
      match (pats, tps0, tps, ts) with
        (pat::pats, tp0::tps0, tp::tps, t::ts) ->
        let isInputParam = match inputParamCount with None -> true | Some n -> index < n in
        match_pat ghostenv env env' isInputParam pat tp0 tp t (fun ghostenv env env' -> match_pats ghostenv env env' (index + 1) pats tps0 tps ts cont)
      | ([], [], [], []) -> cont ghostenv env env'
    in
    let match_coef ghostenv env cont =
      if coef == real_unit && coefpat == real_unit_pat && coef0 == real_unit then cont ghostenv env coef0 [] else
      let match_term_coefpat t =
        let t = real_mul l coef t in
        if definitely_equal t coef0 then
          cont ghostenv env coef0 []
        else
          let half_coef0 = ctxt#mk_real_mul real_half coef0 in
          if definitely_equal t half_coef0 then
            cont ghostenv env half_coef0 [Chunk (g', targs0, half_coef0, ts0, size0)]
          else if ctxt#query (ctxt#mk_real_lt real_zero t) && ctxt#query (ctxt#mk_real_lt t coef0) then
            cont ghostenv env t [Chunk (g', targs0, ctxt#mk_real_sub coef0 t, ts0, size0)]
          else
            if inputParamCount = None then
              None
            else
              assert_false h env l (Printf.sprintf "Fraction mismatch: cannot prove %s == %s or 0 < %s < %s" (ctxt#pprint t) (ctxt#pprint coef0) (ctxt#pprint t) (ctxt#pprint coef0))
      in
      match coefpat with
        SrcPat (LitPat e) -> match_term_coefpat (eval (pn,ilist) None env e)
      | TermPat t -> match_term_coefpat t
      | SrcPat (VarPat x) -> cont (x::ghostenv) (update env x (real_div l coef0 coef)) coef0 []
      | SrcPat DummyPat ->
        if is_dummy_frac_term coef0 then
          cont ghostenv env (get_dummy_frac_term ()) [Chunk (g', targs0, get_dummy_frac_term (), ts0, size0)]
        else
          cont ghostenv env coef0 []
    in
    if not (predname_eq g g' && List.for_all2 unify targs targs0) then None else
    match_pats ghostenv env env' 0 pats tps0 tps ts0 $. fun ghostenv env env' ->
    match_coef ghostenv env $. fun ghostenv env coef0 newChunks ->
    Some (coef0, ts0, size0, ghostenv, env, env', newChunks)
  in
  
  let lookup_points_to_chunk_core h0 f_symb t =
    let rec iter h =
      match h with
        [] -> None
      | Chunk ((g, true), targs, coef, [t0; v], _)::_ when g == f_symb && definitely_equal t0 t -> Some v
      | _::h -> iter h
    in
    iter h0
  in

  let lookup_points_to_chunk h0 env l f_symb t =
    match lookup_points_to_chunk_core h0 f_symb t with
      None -> assert_false h0 env l ("No matching heap chunk: " ^ ctxt#pprint f_symb)
    | Some v -> v
  in

  let read_field h env l t f =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
    lookup_points_to_chunk h env l f_symb t
  in
  
  let pointer_pred_symb () =
    let (_, _, _, _, pointer_pred_symb, _) = List.assoc "pointer" predfammap in
    pointer_pred_symb
  in
  
  let int_pred_symb () =
    let (_, _, _, _, int_pred_symb, _) = List.assoc "integer" predfammap in
    int_pred_symb
  in
  
  let char_pred_symb () =
    let (_, _, _, _, char_pred_symb, _) = List.assoc "character" predfammap in
    char_pred_symb
  in
  
  let pointee_pred_symb l pointeeType =
    match pointeeType with
      PtrType _ -> pointer_pred_symb ()
    | IntType -> int_pred_symb ()
    | Char -> char_pred_symb ()
    | _ -> static_error l "Dereferencing pointers of this type is not yet supported."
  in
  
  let deref_pointer h env l pointerTerm pointeeType =
    lookup_points_to_chunk h env l (pointee_pred_symb l pointeeType) pointerTerm
  in
  
  let assert_chunk_core rules (pn,ilist) h ghostenv env env' l g targs coef coefpat inputParamCount pats tps0 tps cont =
    let rec assert_chunk_core_core h =
      let rec iter hprefix h =
        match h with
          [] -> []
        | chunk::h ->
            match match_chunk (pn,ilist) ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps chunk with
              None -> iter (chunk::hprefix) h
            | Some (coef, ts, size, ghostenv, env, env', newChunks) -> [(newChunks @ hprefix @ h, coef, ts, size, ghostenv, env, env')]
      in
      match iter [] h with
        [] ->
        begin fun cont ->
          if inputParamCount = None || coef != real_unit then cont () else
          begin fun cont' ->
            let Some inputParamCount = inputParamCount in
            let rec iter n ts pats tps0 tps =
              if n = 0 then cont' (List.rev ts) else
              match (pats, tps0, tps) with
              | (pat::pats, tp0::tps0, tp::tps) ->
                let ok t = iter (n - 1) (prover_convert_term t tp0 tp::ts) pats tps0 tps in
                match pat with
                  SrcPat (LitPat e) -> ok (eval (pn,ilist) None env e)
                | TermPat t -> ok t
                | _ -> cont ()
            in
            iter inputParamCount [] pats tps0 tps
          end $. fun ts ->
          match g with
            (g, true) ->
            begin match try_assq g rules with
              Some rules ->
              let rec iter rules =
                match rules with
                  [] -> cont ()
                | (rule_match_func, rule_exec_func)::rules ->
                  if rule_match_func h targs ts then
                    rule_exec_func h targs ts $. fun h ->
                    with_context (Executing (h, env, l, "Consuming chunk (retry)")) $. fun () ->
                    assert_chunk_core_core h
                  else
                    iter rules
              in
              iter rules
            | None -> cont ()
            end
          | _ -> cont ()
        end $. fun () -> assert_false h env l ("No matching heap chunks: " ^ (match g with (g, _) -> ctxt#pprint g))
  (*      
      | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
      | _ -> assert_false h env l "Multiple matching heap chunks."
  *)
      | (h, coef, ts, size, ghostenv, env, env')::_ -> cont h coef ts size ghostenv env env'
    in
    assert_chunk_core_core h
  in
  
  let assert_chunk rules (pn,ilist) h ghostenv env env' l g targs coef coefpat inputParamCount pats cont =
    let tps = List.map (fun _ -> IntType) pats in (* dummies *)
    assert_chunk_core rules (pn,ilist) h ghostenv env env' l g targs coef coefpat inputParamCount pats tps tps cont
  in
  
  let srcpat pat = SrcPat pat in
  let srcpats pats = List.map srcpat pats in
  
  let rec assert_pred_core rules tpenv (pn,ilist) h ghostenv env env' p checkDummyFracs coef cont =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ -> with_context (Executing (h, env, pred_loc p, "Consuming assertion")) cont
    in
    (*
    let time0 = Sys.time() in
    printff "%s: Consuming assertion (timestamp: %f)\n" (string_of_loc (pred_loc p)) time0;
    let cont h ghostenv env size =
      printff "%s: Done consuming assertion (%f seconds)\n" (string_of_loc (pred_loc p)) (Sys.time() -. time0); 
      cont h ghostenv env size
    in
    *)
    with_context_helper (fun _ ->
    let ev = eval (pn,ilist) None env in
    let check_dummy_coefpat l coefpat coef =
      if language = CLang && checkDummyFracs then
      match coefpat with
        SrcPat DummyPat -> if not (is_dummy_frac_term coef) then assert_false h env l "Cannot match a non-dummy fraction chunk against a dummy fraction pattern. First leak the chunk using the 'leak' command."
      | _ -> ()
    in
    let access l coefpat e f rhs =
      let (_, (_, _, _, _, symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
      assert_chunk rules (pn,ilist) h ghostenv env env' l (symb, true) [] coef coefpat (Some 1) [SrcPat (LitPat e); rhs]
        (fun h coef ts size ghostenv env env' -> check_dummy_coefpat l coefpat coef; cont h ghostenv env env' size)
    in
    let callpred l coefpat g targs pats0 pats =
      let g_symb =
        match try_assoc' (pn,ilist) g#name predfammap with
          Some (_, _, _, _, symb, _) -> (symb, true)
        | None -> (List.assoc (g#name) env, false)
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv g#domain in
      let inputParamCount = match g#inputParamCount with None -> None | Some n -> Some (List.length pats0 + n) in
      assert_chunk_core rules (pn,ilist) h ghostenv env env' l g_symb targs coef coefpat inputParamCount (pats0 @ pats) g#domain domain (fun h coef ts size ghostenv env env' ->
        check_dummy_coefpat l coefpat coef;
        cont h ghostenv env env' size
      )
    in
    match p with
    | Access (l, e, f, rhs) -> access l real_unit_pat e f (SrcPat rhs)
    | WCallPred (l, g, targs, pats0, pats) -> callpred l real_unit_pat g targs (srcpats pats0) (srcpats pats)
    | ExprPred (l, Operation (lo, Eq, [Var (lx, x, scope); e], tps)) when !scope = Some LocalVar ->
      begin match try_assoc x env with
        Some t -> assert_term (ctxt#mk_eq t (ev e)) h env l "Cannot prove condition."; cont h ghostenv env env' None
      | None -> let binding = (x, ev e) in cont h ghostenv (binding::env) (binding::env') None
      end
    | ExprPred (l, e) ->
      assert_expr (pn,ilist) env e h env l "Cannot prove condition."; cont h ghostenv env env' None
    | Sep (l, p1, p2) ->
      assert_pred_core rules tpenv (pn,ilist) h ghostenv env env' p1 checkDummyFracs coef (fun h ghostenv env env' size ->
        assert_pred_core rules tpenv (pn,ilist) h ghostenv env env' p2 checkDummyFracs coef (fun h ghostenv env env' _ ->
          cont h ghostenv env env' size
        )
      )
    | IfPred (l, e, p1, p2) ->
      let cont h _ _ env'' _ = cont h ghostenv (env'' @ env) (env'' @ env') None in
      let env' = [] in
      branch
        (fun _ ->
           assume (ev e) (fun _ ->
             assert_pred_core rules tpenv (pn,ilist) h ghostenv env env' p1 checkDummyFracs coef cont))
        (fun _ ->
           assume (ctxt#mk_not (ev e)) (fun _ ->
             assert_pred_core rules tpenv (pn,ilist) h ghostenv env env' p2 checkDummyFracs coef cont))
    | SwitchPred (l, e, cs) ->
      let cont h _ _ env'' _ = cont h ghostenv (env'' @ env) (env'' @ env') None in
      let env' = [] in
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
                     let term' = convert_provertype term proverType ProverInductive in
                     (x, term', term)
                  )
                  pts
              in
              let xs = List.map (fun (x, t, _) -> t) xts in
              let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
              (xs, xenv)
          in
          branch
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym xs) (fun _ -> assert_pred_core rules tpenv (pn,ilist) h (pats @ ghostenv) (xenv @ env) env' p checkDummyFracs coef cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpPred l -> cont h ghostenv env env' None
    | CoefPred (l, coefpat, Access (_, e, f, rhs)) -> access l (SrcPat coefpat) e f (SrcPat rhs)
    | CoefPred (l, coefpat, WCallPred (_, g, targs, pat0, pats)) -> callpred l (SrcPat coefpat) g targs (srcpats pat0) (srcpats pats)
    )
  in
  
  let assert_pred rules tpenv (pn,ilist) h ghostenv env p checkDummyFracs coef cont =
    assert_pred_core rules tpenv (pn,ilist) h ghostenv env [] p checkDummyFracs coef (fun h ghostenv env env' size_first -> cont h ghostenv env size_first)
  in

  let term_of_pred_index =
    match language with
      Java -> fun cn -> List.assoc cn classterms
    | CLang -> fun fn -> List.assoc fn funcnameterms
  in
  
  let contains_edges =
    flatmap
      begin fun (((p, fns), (env, l, predinst_tparams, xs, inputParamCount, wbody)) as predinst) ->
        let (_, _, _, _, symb, _) = List.assoc p predfammap in
        let indexCount = List.length fns in
        let fsymbs = List.map term_of_pred_index fns in
        match inputParamCount with
          None -> []
        | Some n ->
          let inputVars = List.map fst (take n xs) in
          let rec iter wbody =
            match wbody with
              Access (_, e, f, v) ->
              if expr_is_fixed inputVars e then
                let (_, (_, _, _, [tp; _], symb', _)) = List.assoc (f#parent, f#name) field_pred_map in
                [(symb, fsymbs, symb', [], [tp], [e], predinst)]
              else
                []
            | WCallPred (_, g, targs, pats0, pats) ->
              if pats0 <> [] then [] else
              begin match try_assoc g#name predfammap with
                None -> []
              | Some (_, tparams, _, tps, symb', _) ->
                begin match g#inputParamCount with
                  None -> []
                | Some n' ->
                  let Some tpenv = zip tparams targs in
                  let inputArgs = List.map (fun (LitPat e) -> e) (take n' pats) in
                  if List.for_all (fun e -> expr_is_fixed inputVars e) inputArgs then
                    [(symb, fsymbs, symb', targs, List.map (instantiate_type tpenv) (take n' tps), inputArgs, predinst)]
                  else
                    []
                end
              end
            | Sep (_, asn1, asn2) ->
              iter asn1 @ iter asn2
            | IfPred (_, _, asn1, asn2) ->
              iter asn1 @ iter asn2
            | SwitchPred (_, _, cs) ->
              flatmap (fun (SwitchPredClause (_, _, _, _, asn)) -> iter asn) cs
            | _ -> []
          in
          iter wbody
      end
      predinstmap
  in
  
  let rules =
    let rulemap = ref [] in
    let add_rule predSymb rule =
      match try_assq predSymb !rulemap with
        None ->
        rulemap := (predSymb, ref [rule])::!rulemap
      | Some rules ->
        rules := rule::!rules
    in
    let (pn, ilist) = ("", []) in
    List.iter
      begin fun (symb, fsymbs, symb', targs, inputExprTypes, inputExprs, ((p, fns), (env, l, predinst_tparams, xs, inputParamCount, wbody))) ->
        let g = (symb, true) in
        let indexCount = List.length fns in
        let Some n = inputParamCount in
        let (inputParams, outputParams) = take_drop n xs in
        let n' = List.length inputExprs in
        let chunks_match symb1 targs1 ts1 symb2 targs2 ts2 =
          symb1 == symb && symb2 == symb' &&
          let (indices1, args1) = take_drop indexCount ts1 in
          let inputArgs1 = take n args1 in
          List.for_all2 definitely_equal indices1 fsymbs &&
          let Some tpenv = zip predinst_tparams targs1 in
          let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs1 in
          targs2 = List.map (instantiate_type tpenv) targs &&
          let inputArgs2 = List.map2 (fun e tp0 -> let tp = instantiate_type tpenv tp0 in prover_convert_term (eval (pn,ilist) None env e) tp0 tp) inputExprs inputExprTypes in
          List.for_all2 definitely_equal (take n' ts2) inputArgs2
        in
        let autoclose_rule =
          let match_func h targs ts =
            List.exists (fun (Chunk ((g', is_symb), targs', coef', ts', _)) -> is_symb && coef' == real_unit && chunks_match symb targs ts g' targs' ts') h
          in
          let exec_func h targs ts cont =
            let rules = [] in
            let (indices, inputArgs) = take_drop indexCount ts in
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
            let ghostenv = [] in
            let checkDummyFracs = true in
            let coef = real_unit in
            with_context (Executing (h, env, l, "Auto-closing predicate")) $. fun () ->
            assert_pred rules tpenv (pn,ilist) h ghostenv env wbody checkDummyFracs coef $. fun h ghostenv env size_first ->
            let outputArgs = List.map (fun (x, tp0) -> let tp = instantiate_type tpenv tp0 in (prover_convert_term (List.assoc x env) tp0 tp)) outputParams in
            with_context (Executing (h, [], l, "Producing auto-closed chunk")) $. fun () ->
            cont (Chunk (g, targs, coef, inputArgs @ outputArgs, None)::h)
          in
          (match_func, exec_func)
        in
        add_rule symb autoclose_rule;
        let autoopen_rule =
          let match_func h targs ts =
            List.exists (fun (Chunk ((g', is_symb), targs', coef', ts', _)) -> is_symb && coef' == real_unit && chunks_match g' targs' ts' symb' targs ts) h
          in
          let exec_func h targs ts cont =
            let (h, targs, ts) =
              let rec iter hdone htodo =
                match htodo with
                  (Chunk ((g', is_symb), targs', coef', ts', _) as chunk)::htodo ->
                  if is_symb && coef' == real_unit && chunks_match g' targs' ts' symb' targs ts then
                    (hdone @ htodo, targs', ts')
                  else
                    iter (chunk::hdone) htodo
              in
              iter [] h
            in
            let (indices, args) = take_drop indexCount ts in
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) xs args in
            let ghostenv = [] in
            with_context (Executing (h, env, l, "Auto-opening predicate")) $. fun () ->
            assume_pred tpenv (pn,ilist) h ghostenv env wbody real_unit None None $. fun h ghostenv env ->
            cont h
          in
          (match_func, exec_func)
        in
        add_rule symb' autoopen_rule
      end
      contains_edges;
    List.map (fun (predSymb, rules) -> (predSymb, !rules)) !rulemap
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
    | ProduceLemmaFunctionPointerChunkStmt (l, x, body) ->
      begin
        match body with
          None -> []
        | Some s -> assigned_variables s
      end
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) -> []
    | SwitchStmt (l, e, cs) -> flatmap (fun (SwitchStmtClause (_, _, _, ss)) -> block_assigned_variables ss) cs
    | Assert (l, p) -> []
    | Leak (l, p) -> []
    | Open (l, g, targs, ps0, ps1, coef) -> []
    | Close (l, g, targs, ps0, ps1, coef) -> []
    | ReturnStmt (l, e) -> []
    | WhileStmt (l, e, p, ss, _) -> block_assigned_variables ss
    | Throw (l, e) -> []
    | TryCatch (l, body, catches) -> block_assigned_variables body @ flatmap (fun (l, t, x, body) -> block_assigned_variables body) catches
    | TryFinally (l, body, lf, finally) -> block_assigned_variables body @ block_assigned_variables finally
    | BlockStmt (l, ds, ss) -> block_assigned_variables ss
    | PerformActionStmt (lcb, nonpure_ctxt, bcn, pre_boxargs, lch, pre_handlepredname, pre_handlepredargs, lpa, actionname, actionargs, atomic, body, closeBraceLoc, post_boxargs, lph, post_handlepredname, post_handlepredargs) ->
      block_assigned_variables body
    | SplitFractionStmt (l, p, targs, pats, coefopt) -> []
    | MergeFractionsStmt (l, p, targs, pats) -> []
    | CreateBoxStmt (l, x, bcn, es, handleClauses) -> []
    | CreateHandleStmt (l, x, hpn, e) -> []
    | DisposeBoxStmt (l, bcn, pats, handleClauses) -> []
    | GotoStmt _ -> []
    | NoopStmt _ -> []
    | LabelStmt _ -> []
    | InvariantStmt _ -> []
  in

  let dummypat = SrcPat DummyPat in
  
  let get_points_to (pn,ilist) h p predSymb l cont =
    assert_chunk rules (pn,ilist) h [] [] [] l (predSymb, true) [] real_unit dummypat (Some 1) [TermPat p; dummypat] (fun h coef [_; t] size ghostenv env env' ->
      cont h coef t)
  in
    
  let get_field (pn,ilist) h t f l cont =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
    get_points_to (pn,ilist) h t f_symb l cont
  in
  
  let current_thread_name = "currentThread" in
  let current_thread_type = IntType in
  
  (* Region: function contracts *)
  
  let functypemap1 =
    let rec iter functypemap ds =
      match ds with
        [] -> List.rev functypemap
      | (ftn, (l, gh, rt, ftxmap, xmap, pre, post))::ds ->
        let (pn,ilist) = ("",[]) in
        let (pre, post) =
          let (wpre, tenv) = check_pred (pn,ilist) [] (ftxmap @ xmap @ [("this", PtrType Void); (current_thread_name, current_thread_type)]) pre in
          let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
          let (wpost, tenv) = check_pred (pn,ilist) [] postmap post in
          (wpre, wpost)
        in
        iter ((ftn, (l, gh, rt, ftxmap, xmap, pre, post))::functypemap) ds
      | _::ds -> iter functypemap ds
    in
    iter [] functypedeclmap1
  in
  
  let functypemap = functypemap1 @ functypemap0 in
  
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
    | _ ->
    with_context (Executing (h, env, l, "Cleaning up dummy fraction chunks")) $. fun () ->
    let h = List.filter (fun (Chunk (_, _, coef, _, _)) -> not (is_dummy_frac_term coef)) h in
    with_context (Executing (h, env, l, "Leak check.")) $. fun () ->
    if h <> [] then assert_false h env l msg;
    check_breakpoint [] env l
  in
  
  let check_func_header_compat (pn,ilist) l msg env00 (k, tparams, rt, xmap, atomic, pre, post) (k0, tparams0, rt0, xmap0, atomic0, cenv0, pre0, post0) =
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
      (if (List.length xmap) > (List.length xmap0) then static_error l (msg ^ "Implementation has more parameters than prototype."));
      List.iter 
        (fun ((x, t), (x0, t0)) ->
           expect_type_core (pn,ilist) l (msg ^ "Parameter '" ^ x ^ "': ") t0 (instantiate_type tpenv t);
        )
        (zip2 xmap xmap0)
    end;
    if atomic <> atomic0 then static_error l (msg ^ "Atomic clauses do not match.");
    push();
    let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
    let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
    let env0 = currentThreadEnv @ env0_0 @ cenv0 in
    assume_pred [] (pn,ilist) [] [] env0 pre0 real_unit None None (fun h _ env0 ->
      let bs = zip2 xmap env0_0 in
      let env = currentThreadEnv @ List.map (fun ((p, _), (p0, v)) -> (p, v)) bs @ env00 in
      assert_pred rules tpenv (pn,ilist) h [] env pre true real_unit (fun h _ env _ ->
        let (env, env0) =
          match rt with
            None -> (env, env0)
          | Some t -> let result = get_unique_var_symb "result" t in (("result", result)::env, ("result", result)::env0)
        in
        assume_pred tpenv (pn,ilist) h [] env post real_unit None None (fun h _ _ ->
          assert_pred rules [] (pn,ilist) h [] env0 post0 true real_unit (fun h _ env0 _ ->
            check_leaks h env0 l (msg ^ "Implementation leaks heap chunks.")
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
  
  let functypes_implemented = ref [] in
  
  let check_func_header pn ilist tparams0 tenv0 env0 l k tparams rt fn fterm xs atomic functype_opt contract_opt body =
    if tparams0 <> [] then static_error l "Declaring local functions in the scope of type parameters is not yet supported.";
    check_tparams l tparams0 tparams;
    let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) tparams rt) in
    let xmap =
      let rec iter xm xs =
        match xs with
          [] -> List.rev xm
        | (te, x)::xs ->
          if List.mem_assoc x xm then static_error l "Duplicate parameter name.";
          if List.mem_assoc x tenv0 then static_error l ("Parameter '" ^ x ^ "' hides existing variable '" ^ x ^ "'.");
          let t = check_pure_type (pn,ilist) tparams te in
          iter ((x, t)::xm) xs
      in
      iter [] xs
    in
    let tenv = [(current_thread_name, current_thread_type)] @ xmap @ tenv0 in
    let (pre, pre_tenv, post) =
      match contract_opt with
        None -> static_error l "Non-fixpoint function must have contract."
      | Some (pre, post) ->
        let (wpre, pre_tenv) = check_pred (pn,ilist) tparams tenv pre in
        let postmap = match rt with None -> pre_tenv | Some rt -> ("result", rt)::pre_tenv in
        let (wpost, tenv) = check_pred (pn,ilist) tparams postmap post in
        (wpre, pre_tenv, wpost)
    in
    if atomic && body <> None then static_error l "Implementing atomic functions is not yet supported.";
    begin
      match functype_opt with
        None -> ()
      | Some (ftn, ftargs) ->
        if body = None then static_error l "A function prototype cannot implement a function type.";
        begin
          match try_assoc ftn functypemap with
            None -> static_error l "No such function type."
          | Some (lft, gh, rt0, ftxmap0, xmap0, pre0, post0) ->
            let ftargenv =
              match zip ftxmap0 ftargs with
                None -> static_error l "Incorrect number of function type arguments"
              | Some bs ->
                List.map
                  begin fun ((x, tp), (larg, arg)) ->
                    let value =
                      match try_assoc arg modulemap with
                        None -> static_error larg "No such module"
                      | Some term -> term
                    in
                    expect_type (pn,ilist) larg IntType tp;
                    (x, value)
                  end
                  bs
            in
            let Some fterm = fterm in
            let cenv0 = [("this", fterm)] @ ftargenv in
            let k' = match gh with Real -> Regular | Ghost -> Lemma in
            check_func_header_compat (pn,ilist) l "Function type implementation check: " env0
              (k, tparams, rt, xmap, atomic, pre, post)
              (k', [], rt0, xmap0, false, cenv0, pre0, post0);
            if gh = Real then
            begin
              if ftargs = [] then
                assume_is_functype fn ftn;
              if not (List.mem_assoc ftn functypemap1) then
                functypes_implemented := (fn, lft, ftn, List.map snd ftargs, unloadable)::!functypes_implemented
            end
        end
    end;
    (rt, xmap, pre, pre_tenv, post)
  in
  
  let (funcmap1, prototypes_implemented) =
    let rec iter pn ilist funcmap prototypes_implemented ds =
      match ds with
        [] -> (funcmap, List.rev prototypes_implemented)
      | Func (l, k, tparams, rt, fn, xs, atomic, functype_opt, contract_opt, body,Static,Public)::ds when k <> Fixpoint ->
        let fn = full_name pn fn in
        let fterm = if language = CLang then Some (List.assoc fn funcnameterms) else None in
        let (rt, xmap, pre, pre_tenv, post) =
          check_func_header pn ilist [] [] [] l k tparams rt fn fterm xs atomic functype_opt contract_opt body
        in
        begin
          let body' = match body with None -> None | Some body -> Some (Some body) in
          match try_assoc2 fn funcmap funcmap0 with
            None -> iter pn ilist ((fn, ([], fterm, l, k, tparams, rt, xmap, atomic, pre, pre_tenv, post, functype_opt, body',Static,Public))::funcmap) prototypes_implemented ds
          | Some ([], fterm0, l0, k0, tparams0, rt0, xmap0, atomic0, pre0, pre_tenv0, post0, _, Some _,Static,Public) ->
            if body = None then
              static_error l "Function prototype must precede function implementation."
            else
              static_error l "Duplicate function implementation."
          | Some ([], fterm0, l0, k0, tparams0, rt0, xmap0, atomic0, pre0, pre_tenv0, post0, functype_opt0, None,Static,Public) ->
            if body = None then static_error l "Duplicate function prototype.";
            check_func_header_compat (pn,ilist) l "Function prototype implementation check: " [] (k, tparams, rt, xmap, atomic, pre, post) (k0, tparams0, rt0, xmap0, atomic0, [], pre0, post0);
            iter pn ilist ((fn, ([], fterm, l, k, tparams, rt, xmap, atomic, pre, pre_tenv, post, functype_opt, body',Static,Public))::funcmap) ((fn, l0)::prototypes_implemented) ds
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
               let (pre, pre_tenv, post) =
                 match co with
                   None -> static_error lm ("Non-fixpoint function must have contract: "^n)
                 | Some (pre, post) ->
                   let (pre, tenv) = check_pred (pn,ilist) [] ((current_thread_name, current_thread_type)::xmap) pre in
                   let postmap = match check_t t with None -> tenv | Some rt -> ("result", rt)::tenv in
                   let (post, _) = check_pred (pn,ilist) [] postmap post in
                   (pre, tenv, post)
               in
               iter ((n, (lm,check_t t, xmap, pre, pre_tenv, post,fb,v))::mmap) meths
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
              | (mn, (lm0,rt0,xmap0,pre0,pre_tenv0,post0,fb0,v0)) as elem::rest ->
                match try_assoc mn meths1 with
                  None-> iter rest (elem::meths1)
                | Some(lm1,rt1,xmap1,pre1,pre_tenv1,post1,fb1,v1) -> 
                  check_func_header_compat (pn1,ilist1) lm1 "Method specification check: " [] (Regular,[],rt1, xmap1,false, pre1, post1) (Regular, [], rt0, xmap0, false, [], pre0, post0);
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
                 | (g,(_,_,c,_,_,_,_,_,_))::crest ->(if n==g then equal_types x c else false)|| search_equal x crest
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
               let (pre, pre_tenv, post) =
                 let rec search_interf i=
                   match i with
                    [] ->
                    (match co with
                       None ->static_error lm ("Non-fixpoint function must have contract: "^n)
                     | Some (pre, post) -> 
                       let (wpre, tenv) = check_pred (pn,ilist) [] ((current_thread_name, current_thread_type)::xmap) pre in
                       let postmap = match check_t t with None -> tenv | Some rt -> ("result", rt)::tenv in
                       let (wpost, _) = check_pred (pn,ilist) [] postmap post in
                       (wpre, tenv, wpost)
                    )
                  | name::rest ->
                    match try_assoc' (pn,ilist) name interfmap with
                      None -> search_interf rest
                    | Some(_,meth_specs,_,_) -> match try_assoc n meth_specs with
                        None -> search_interf rest
                      | Some(_,rt', xmap', pre, pre_tenv, post,Instance,v) -> match co with
                          None -> matchargs xmap xmap';(pre,pre_tenv,post)
                        | Some(pre0,post0)->
                            let (wpre, tenv) = check_pred (pn,ilist) [] ((current_thread_name, current_thread_type)::xmap) pre0 in
                            let postmap = match check_t t with None -> tenv | Some rt -> ("result", rt)::tenv in
                            let (wpost, _) = check_pred (pn,ilist) [] postmap post0 in
                            push();
                            let ("this", thisType)::xmap = xmap in
                            let ("this", _)::xmap' = xmap' in
                            let thisTerm = get_unique_var_symb "this" thisType in
                            assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) (fun _ ->
                              check_func_header_compat (pn,ilist) l "Method specification check: " [("this", thisTerm)]
                                (Regular, [], check_t t, xmap, false, wpre, wpost)
                                (Regular, [], rt', xmap', false, [("this", thisTerm)], pre, post)
                            );
                            pop();
                            (wpre, tenv, wpost)
                 in
                 search_interf interfs
               in
               let ss' = match ss with None -> None | Some ss -> Some (Some ss) in
               (if n="main" then
                 match pre with ExprPred(lp,pre) -> match post with ExprPred(lp',post) ->
                   match pre with 
                     True(_) -> 
                       match post with
                         True(_) -> main_meth:=(cn,l)::!main_meth
                       | _ -> static_error lp' "The postcondition of the main method must be 'true'" 
                   | _ -> static_error lp "The precondition of the main method must be 'true'"
                );
               iter ((n, (lm,check_t t, xmap, pre, pre_tenv, post, ss',fb,v))::mmap) meths
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
               let (pre, pre_tenv, post) =
                 match co with
                   None -> static_error lm "Constructor must have contract: "
                 | Some (pre, post) ->
                     let (wpre, tenv) = check_pred (pn,ilist) [] xmap pre in
                     let postmap = ("result", ObjType(cn))::tenv in
                     let (wpost, _) = check_pred (pn,ilist) [] postmap post in
                     (wpre, tenv, wpost)
               in
               let ss' = match ss with None -> None | Some ss -> Some (Some ss) in
               iter ((xmap, (lm,pre,pre_tenv,post,ss',v))::cmap) constr
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
              | (n, (lm0,rt0,xmap0,pre0,pre_tenv0,post0,ss0,fb0,v0)) as elem::rest ->
                match try_assoc n meths1 with
                  None-> iter rest (elem::meths1)
                | Some(lm1,rt1,xmap1,pre1,pre_tenv1,post1,ss1,fb1,v1) -> 
                  check_func_header_compat (pn1,ilist1) lm1 "Method implementation check: " [] (Regular,[],rt1, xmap1,false, pre1, post1) (Regular, [], rt0, xmap0, false, [], pre0, post0);
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
              | (xmap0, (lm0,pre0,pre_tenv0,post0,ss0,v0)) as elem::rest ->
                match try_assoc xmap0 constr1 with
                  None-> iter rest (elem::constr1)
                | Some(lm1,pre1,pre_tenv1,post1,ss1,v1) ->
                  let rt= Some (ObjType(cn)) in
                  check_func_header_compat (pn1,ilist1) lm1 "Constructor implementation check: " [] (Regular,[],rt, xmap0,false, pre1, post1) (Regular, [], rt, xmap0, false, [], pre0, post0);
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
  
  (* Region: symbolic execution helpers *)
  
  (* locals whose address is taken in e *)
  let rec locals_address_taken e =
    match e with
      True(_) -> []
    | False(_) -> []
    | Null(_) -> []
    | Var(_, _, _) -> []
    | Operation(l, op, [e1; e2], _) -> List.append (locals_address_taken e1) (locals_address_taken e2)
    | IntLit(_, _, _) -> []
    | StringLit(_, _) -> []
    | ClassLit(_, _) -> []
    | Read(_, e, _) -> locals_address_taken e
    | Deref(_, e, _) -> locals_address_taken e
    | CallExpr(l, name, targs, _, args, binding) ->  List.flatten (List.map (fun pat -> match pat with LitPat(e) -> locals_address_taken e | _ -> []) args)
    | IfExpr(_, con, e1, e2) -> (locals_address_taken con) @ (locals_address_taken e1) @ (locals_address_taken e2)
    | SwitchExpr(_, e, clauses, _) -> (locals_address_taken e) @
        (List.flatten (List.map (fun clause -> match clause with SwitchExprClause(_, _, _, e) -> locals_address_taken e) clauses))
    | AddressOf(_, Var(_, x, scope)) when !scope = Some(LocalVar) -> [x]
    | AddressOf(_, e) -> locals_address_taken e
    | PredNameExpr(_, _) -> []
    | CastExpr(_, _, e) -> locals_address_taken e
    | SizeofExpr(_, _) -> []
    | ProverTypeConversion(_, _, e) -> locals_address_taken e
  in
  
  let rec locals_address_taken_stmt s =
    match s with
      PureStmt(_, s) -> locals_address_taken_stmt s (* can we take the address of a local in here? *)
    | NonpureStmt(_, _, s) -> locals_address_taken_stmt s
    | Assign(_, _, e) -> locals_address_taken e
    | DeclStmt(_, _, _, e) -> locals_address_taken e
    | Write(_, e1, f, e2) -> (locals_address_taken e1) @ (locals_address_taken e2)
    | WriteDeref(_, e1, e2) -> (locals_address_taken e1) @ (locals_address_taken e2)
    | CallStmt(_, _, _, args, _) -> List.flatten (List.map (fun e -> locals_address_taken e) args)
    | IfStmt(_, e, thn, els) -> (locals_address_taken e) @ 
        (List.flatten (List.map (fun s -> locals_address_taken_stmt s) (thn @ els)))
    | SwitchStmt(_, e, clauses) -> (locals_address_taken e) @ 
        (List.flatten (List.map (fun c -> match c with SwitchStmtClause(_, _, _, stmts) -> 
          List.flatten (List.map (fun s -> locals_address_taken_stmt s) stmts)
        ) clauses))
    | Assert(_, p) -> [] (* should we look inside predicates as well? *)
    | Leak(_, p) -> []
    | Open(_, _, _, _, _, _) -> []
    | Close(_, _, _, _, _, _) -> []
    | ReturnStmt(_, e) -> (match e with None -> [] | Some(e) -> locals_address_taken e)
    | WhileStmt(_, e, inv, body, _) -> (locals_address_taken e) @ 
        (List.flatten (List.map (fun s -> locals_address_taken_stmt s) body))
    | BlockStmt(_, decls, body) -> (List.flatten (List.map (fun s -> locals_address_taken_stmt s) body))
    | _ -> [] (* todo *)
  in
 
  let nonempty_pred_symbs = List.map (fun (_, (_, (_, _, _, _, symb, _))) -> symb) field_pred_map in
  
  let eval_non_pure (pn,ilist) is_ghost_expr h env e =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg -> assert_term t h env l msg) in
    eval_core (pn,ilist) assert_term (Some ((fun l t f -> read_field h env l t f), (fun l p t -> deref_pointer h env l p t))) env e
  in 
  
  let rec eval_h (pn,ilist) is_ghost_expr h env e cont =
    let rec iter h e cont =
    match e with
      StringLit (l, s)->
      begin match file_type path with
        Java ->
        let value = get_unique_var_symb "stringLiteral" (ObjType "java.lang.String") in
        assume_neq value (ctxt#mk_intlit 0) (fun () ->
          cont h value
        )
      | _ ->
        if unloadable then static_error l "The use of string literals as expressions in unloadable modules is not supported. Put the string literal in a named global array variable instead.";
        let (_, _, _, _, chars_symb, _) = List.assoc "chars" predfammap in
        let (_, _, _, _, mem_symb) = List.assoc "mem" purefuncmap in
        let (_, _, _, _, nil_symb) = List.assoc "nil" purefuncmap in
        let (_, _, _, _, cons_symb) = List.assoc "cons" purefuncmap in
        let cs = get_unique_var_symb "stringLiteralChars" (InductiveType ("list", [Char])) in
        let value = get_unique_var_symb "stringLiteral" (PtrType Char) in
        let rec string_to_term s = 
          if String.length s == 0 then
              ctxt#mk_app cons_symb [ctxt#mk_boxed_int (ctxt#mk_intlit 0); ctxt#mk_app nil_symb []]
          else
            ctxt#mk_app cons_symb [ctxt#mk_boxed_int (ctxt#mk_intlit (Char.code (String.get s 0))); string_to_term (String.sub s 1 (String.length s - 1))]
        in
        let coef = get_dummy_frac_term () in
        assume (ctxt#mk_app mem_symb [ctxt#mk_boxed_int (ctxt#mk_intlit 0); cs]) (fun () ->     (* mem(0, cs) == true *)
          assume (ctxt#mk_not (ctxt#mk_eq value (ctxt#mk_intlit 0))) (fun () ->
            assume (ctxt#mk_eq (string_to_term s) cs) (fun () ->
              cont (Chunk ((chars_symb, true), [], coef, [value; cs], None)::h) value
            )
          )
        )
      end
    | Operation (l, Add, [e1; e2], t) when !t = Some [ObjType "java.lang.String"; ObjType "java.lang.String"] ->
      (* Note: we don't even have to evaluate the arguments. *)
      let value = get_unique_var_symb "string" (ObjType "java.lang.String") in
      assume_neq value (ctxt#mk_intlit 0) $. fun () ->
      cont h value
    | Read (l, e, f) ->
      iter h e $. fun h t ->
      let (_, (_, _, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
      begin match lookup_points_to_chunk_core h f_symb t with
        None -> (* Try the heavyweight approach; this might trigger a rule (i.e. an auto-open or auto-close) and rewrite the heap. *)
        get_points_to (pn,ilist) h t f_symb l $. fun h coef v ->
        cont (Chunk ((f_symb, true), [], coef, [t; v], None)::h) v
      | Some v -> cont h v
      end
    | Operation (l, Not, [e], ts) -> eval_h (pn,ilist) is_ghost_expr h env e (fun h v -> cont h (ctxt#mk_not v))
    | Operation (l, Eq, [e1; e2], ts) -> eval_h (pn,ilist) is_ghost_expr h env e1 (fun h v1 -> 
        eval_h (pn, ilist) is_ghost_expr h env e2 (fun h v2 -> cont h (ctxt#mk_eq v1 v2)))
    | Operation (l, Neq, [e1; e2], ts) -> eval_h (pn,ilist) is_ghost_expr h env e1 (fun h v1 -> 
        eval_h (pn, ilist) is_ghost_expr h env e2 (fun h v2 -> cont h (ctxt#mk_not (ctxt#mk_eq v1 v2))))
    | Operation (l, And, [e1; e2], ts) -> eval_h (pn,ilist) is_ghost_expr h env e1 
      (fun h1 v1 ->
        branch
          (fun _ -> assume (v1) (fun _ -> eval_h (pn,ilist) is_ghost_expr h1 env e2 cont))
          (fun _ -> assume (ctxt#mk_not v1) (fun _ -> cont h1 ctxt#mk_false))
      )
    | Operation (l, Or, [e1; e2], ts) -> 
      eval_h (pn,ilist) is_ghost_expr h env e1 
      (fun h1 v1 ->
        branch
          (fun _ -> assume (v1) (fun _ -> cont h1 ctxt#mk_true))
          (fun _ -> assume (ctxt#mk_not v1) (fun _ -> eval_h (pn,ilist) is_ghost_expr h1 env e2 cont))
      )
    | IfExpr (l, con, e1, e2) ->
      eval_h (pn, ilist) is_ghost_expr h env con (fun h v ->
        branch
          (fun _ -> assume (v) (fun _ -> eval_h (pn,ilist) is_ghost_expr h env e1 cont))
          (fun _ -> assume (ctxt#mk_not v) (fun _ -> eval_h (pn,ilist) is_ghost_expr h env e2 cont))
      )
    | e -> cont h (eval_non_pure (pn,ilist) is_ghost_expr h env e)
    in
    iter h e cont
  in
  
  let prototypes_used : (string * loc) list ref = ref [] in
  
  let register_prototype_used l g =
    if not (List.mem (g, l) !prototypes_used) then
      prototypes_used := (g, l)::!prototypes_used
  in
  
  let assume_is_of_type l t tp cont =
    match tp with
      IntType -> assume (ctxt#mk_and (ctxt#mk_le min_int_term t) (ctxt#mk_le t max_int_term)) cont
    | PtrType _ -> assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) t) (ctxt#mk_le t max_ptr_term)) cont
    | _ -> static_error l (Printf.sprintf "Producing the limits of a variable of type '%s' is not yet supported." (string_of_type tp))
  in
  
  (* Region: verification of calls *)
  
  let verify_call l (pn, ilist) xo g targs pats (callee_tparams, tr, ps, funenv, pre, post, body,v) pure leminfo sizemap h tparams tenv ghostenv env cont =
    let eval0 = eval (pn,ilist) in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure (pn,ilist) pure h env e in
    let eval_h0 = eval_h (pn,ilist) in
    let eval_h h env pat cont =
      match pat with
        SrcPat (LitPat e) -> if not pure then check_ghost ghostenv l e; eval_h (pn,ilist) pure h env e cont
      | TermPat t -> cont h t
    in
    let rec evhs h env pats cont =
      match pats with
        [] -> cont h []
      | pat::pats -> eval_h h env pat (fun h v -> evhs h env pats (fun h vs -> cont h (v::vs)))
    in 
    let ev e = eval env e in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context."
    in
    let vartp l x = match try_assoc x tenv with None -> static_error l ("No such variable: "^x) | Some tp -> tp in
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
          (function
            (SrcPat (LitPat e), (x, t0)) ->
            let t = instantiate_type tpenv t0 in
            SrcPat (LitPat (box (check_expr_t (pn,ilist) tparams tenv e t) t t0))
          | (TermPat t, _) -> TermPat t
          ) bs
    in
    evhs h env ws $. fun h ts ->
    let Some env' = zip ys ts in
    let cenv = [(current_thread_name, List.assoc current_thread_name env)] @ env' @ funenv in
    with_context PushSubcontext (fun () ->
      assert_pred rules tpenv (pn,ilist) h ghostenv cenv pre true real_unit (fun h ghostenv' env' chunk_size ->
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
                      | Chunk ((p, true), _, coef, ts, _)::_ when List.memq p nonempty_pred_symbs && coef == real_unit -> true
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
        assume_pred tpenv (pn,ilist) h ghostenv' env'' post real_unit None None $. fun h _ _ ->
        with_context PopSubcontext $. fun () ->
        begin fun cont ->
          match g with
            Some g when (startswith g "new ") ->
              let Some (result, _) = r in
              let cn = String.sub g 4 ((String.length g)-4) in
              let cn = check_classname (pn, ilist) (l, cn) in
              assume_neq result (ctxt#mk_intlit 0) (fun () ->
                assume_eq (ctxt#mk_app get_class_symbol [result]) (List.assoc cn classterms) (fun () ->
                  cont()
                )
              )
          | _ -> cont()
        end $. fun () ->
        cont h r
      )
    )
  in
  
  let funcnameterm_of funcmap fn =
    let (env, Some fterm, l, k, tparams, rt, ps, atomic, pre, pre_tenv, post, functype_opt, body, _, _) = List.assoc fn funcmap in fterm
  in
  
  (* Region: verification of statements *)
  
  let rec verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont =
    stats#stmtExec;
    let l = stmt_loc s in
    if verbose then printff "%s: Executing statement (timestamp: %f)\n" (string_of_loc l) (Sys.time ());
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
    let vartp l x = 
      match try_assoc x tenv with
          None -> 
        begin
          match try_assoc' (pn, ilist) x globalmap with
            None -> static_error l ("No such variable: "^x)
          | Some((l, tp, symbol)) -> (tp, Some(symbol))
        end 
      | Some tp -> (tp, None) 
    in
    let update_local_or_global h env tpx x symb w cont =
      match symb with
        None -> cont h (update env x w)
      | Some(symb) -> 
          let predSymb = pointee_pred_symb l tpx in
          get_points_to (pn,ilist) h symb predSymb l (fun h coef _ ->
            if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a global variable requires full permission.";
            cont (Chunk ((predSymb, true), [], real_unit, [symb; w], None)::h) env)
    in
    let check_correct xo g targs pats (lg, callee_tparams, tr, ps, funenv, pre, post, body, v) cont =
      verify_call l (pn, ilist) xo g targs (List.map (fun pat -> SrcPat pat) pats) (callee_tparams, tr, ps, funenv, pre, post, body, v) pure leminfo sizemap h tparams tenv ghostenv env cont
    in
    let call_stmt l xo g targs pats fb cont =
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
               match List.hd pats with LitPat (Var(_,x,_)) ->( match vartp l x with (* HACK :) this is altijd 1e argument bij instance method*) (ObjType(class_name), _) ->(class_name,Instance,pats,false))
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
               | (n,(lm,rt, xmap, pre, pre_tenv, post, body,fbm,v))::rest when n=g-> 
                 let match_args xmap pats =
                   match zip pats xmap with
                     None -> false
                   | Some bs ->
                       try List.map(function (LitPat e, (x, tp)) -> check_expr_t (pn,ilist) [] tenv e tp) bs; true
                       with StaticError (l, msg) -> false
                 in
                 if(match_args xmap pats) then
                   if fb <>fbm then static_error l ("Wrong method binding of "^g^" :"^(tostring fb)^" instead of"^(tostring fbm))
                   else check_correct xo (Some g) targs pats (lm, [], rt, xmap, [], pre, post, body,v) cont
                 else
                   search_meth rest
               | _::rest -> search_meth rest
             in
             let rec search_cons clist=
               match clist with
                [] -> static_error l ("Constructor "^g^" not found!")
              | (xmap,(lm,pre,pre_tenv,post,ss,v))::rest->
                let match_args xmap pats =
                  match zip pats xmap with
                    None -> false
                  | Some bs -> 
                      try List.map(function (LitPat e, (x, tp)) -> check_expr_t (pn,ilist) [] tenv e tp) bs; true
                      with StaticError (l, msg) -> false
                in
                if(match_args xmap pats) then
                  check_correct xo (Some g) targs pats (lm, [],Some (ObjType(class_name)), xmap, [], pre, post,ss,Static) cont
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
                   Some(lm,rt, xmap, pre, pre_tenv, post,fbm,v) ->
                    if fb <>fbm 
                      then static_error l ("Wrong function binding of "^g^" :"^(tostring fb)^" instead of"^(tostring fbm));
                      let _ = if pure then static_error l "Cannot call regular functions in a pure context." in
                      check_correct xo (Some g) targs pats (lm, [], rt, xmap, [], pre, post, None,v) cont
                 | None->  static_error l ("Method "^class_name^" not found!!")
                )
            | None ->
                (match try_assoc' (pn,ilist) g funcmap with (* java probleem*)
                   None -> 
                     (match try_assoc' (pn,ilist) g purefuncmap with
                        None -> static_error l ("No such method: " ^ g)
                      | Some (lg, callee_tparams, rt, pts, gs) ->
                        let Some g=search' g (pn,ilist) purefuncmap in
                        let (w, t) = check_expr (pn,ilist) tparams tenv (CallExpr (l, g, targs, [], pats,fb)) in
                        cont h (Some (ev w, t))
                     )
                 | Some (funenv, fterm, lg, k, tparams, tr, ps, atomic, pre, pre_tenv, post, functype_opt, body,fbf,v) ->
                     let g= match search' g (pn,ilist) funcmap with Some s -> s in
                     if fb <>fbf then static_error l ("Wrong function binding "^(tostring fb)^" instead of "^(tostring fbf));
                     if body = None then register_prototype_used lg g;
                     let _ = if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." in
                     let _ = if not pure && k = Lemma then static_error l "Cannot call lemma functions in a non-pure context." in
                     check_correct xo (Some g) targs pats (lg, tparams, tr, ps, funenv, pre, post, body,v) cont
                )
            )
      )
    | _ ->
      (
      match try_assoc g tenv with
        Some (PtrType (FuncType ftn)) ->
        let fterm = List.assoc g env in
        let (_, gh, rt, ftxmap, xmap, pre, post) = List.assoc ftn functypemap in
        if pure && gh = Real then static_error l "Cannot call regular function pointer in a pure context.";
        let check_call h args cont =
          verify_call l (pn, ilist) xo None [] (TermPat fterm::List.map (fun arg -> TermPat arg) args @ List.map (fun pat -> SrcPat pat) pats) ([], rt, (("this", PtrType Void)::ftxmap @ xmap), [], pre, post, None, Public) pure leminfo sizemap h tparams tenv ghostenv env cont
        in
        begin
          match gh with
            Real when ftxmap = [] ->
            let (lg, _, _, _, isfuncsymb) = List.assoc ("is_" ^ ftn) purefuncmap in
            let phi = ctxt#mk_app isfuncsymb [fterm] in
            assert_term phi h env l ("Could not prove is_" ^ ftn ^ "(" ^ g ^ ")");
            check_call h [] cont
          | Real ->
            let (_, _, _, _, predsymb, inputParamCount) = List.assoc ("is_" ^ ftn) predfammap in
            let pats = TermPat fterm::List.map (fun _ -> SrcPat DummyPat) ftxmap in
            assert_chunk rules (pn,ilist) h [] [] [] l (predsymb, true) [] real_unit dummypat inputParamCount pats $. fun h coef (_::args) _ _ _ _ ->
            check_call h args $. fun h retval ->
            cont (Chunk ((predsymb, true), [], coef, fterm::args, None)::h) retval
          | Ghost ->
            let (_, _, _, _, predsymb, _) = List.assoc ("is_" ^ ftn) predfammap in
            assert_chunk rules (pn,ilist) h [] [] [] l (predsymb, true) [] real_unit dummypat (Some 1) [TermPat fterm] $. fun h coef _ _ _ _ _ ->
            if not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk required.";
            check_call h [] $. fun h retval ->
            cont (Chunk ((predsymb, true), [], real_unit, [fterm], None)::h) retval
        end
      | _ ->
      match try_assoc' (pn,ilist) g funcmap with
        None ->
        begin match try_assoc' (pn,ilist) g purefuncmap with
          None -> static_error l ("No such function: " ^ g)
        | Some (lg, callee_tparams, rt, pts, gs) ->
          let (w, t) = check_expr (pn,ilist) tparams tenv (CallExpr (l, g, targs, [], pats,fb)) in
          cont h (Some (ev w, t))
        end
      | Some (funenv, fterm, lg,k, tparams, tr, ps, atomic, pre, pre_tenv, post, functype_opt, body,fbf,v) ->
        if fb <>fbf then static_error l ("Wrong function binding "^(tostring fb)^" instead of "^(tostring fbf));
        if body = None then register_prototype_used lg g;
        let _ = if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." in
        let _ = if not pure && k = Lemma then static_error l "Cannot call lemma functions in a non-pure context." in
        check_correct xo (Some g) targs pats (lg, tparams, tr, ps, funenv, pre, post, body,v) cont
      ) 
    in 
    let verify_expr typ0 xo e cont =
      let l = expr_loc e in
      let check_type h retval =
        begin match (typ0, retval) with
          (Some _, None) -> static_error l "Call does not return a value"
        | (Some typ0, Some (term, typ)) -> expect_type (pn,ilist) l typ typ0
        | (None, _) -> ()
        end;
        cont h retval
      in
      match e with
      | CallExpr (l, "malloc", [], [], args,Static) ->
        begin match args with
          [LitPat (SizeofExpr (lsoe, StructTypeExpr (ltn, tn)))] ->
          let fds =
            match try_assoc tn structmap with
              None -> static_error l "No such struct"
            | Some (_, None, _) -> static_error l "Argument of sizeof cannot be struct type declared without a body."
            | Some (_, Some fds, _) -> fds
          in
          let resultType = PtrType (StructType tn) in
          let result = get_unique_var_symb (match xo with None -> tn | Some x -> x) resultType in
          let cont h = check_type h (Some (result, resultType)) in
          branch
            (fun () ->
               assume_eq result (ctxt#mk_intlit 0) (fun () ->
                 cont h
               )
            )
            (fun () ->
               assume_neq result (ctxt#mk_intlit 0) (fun () ->
                 let rec iter h fds =
                   match fds with
                     [] ->
                     let (_, (_, _, _, _, malloc_block_symb, _)) = (List.assoc tn malloc_block_pred_map)in
                     cont (h @ [Chunk ((malloc_block_symb, true), [], real_unit, [result], None)])
                   | (f, (lf, gh, t))::fds ->
                     let fref = new fieldref f in
                     fref#set_parent tn; fref#set_range t;
                     assume_field h fref result (get_unique_var_symb "value" t) real_unit $. fun h ->
                     iter h fds
                 in
                 iter h fds
               )
            )
        | _ -> call_stmt l xo "malloc" [] args Static check_type
        end
      | CallExpr (lc, g, targs, [], pats,fb) ->
        call_stmt lc xo g targs pats fb check_type
      | e ->
        let (w, t) = match typ0 with None -> check_expr (pn,ilist) tparams tenv e | Some tpx -> (check_expr_t (pn,ilist) tparams tenv e tpx, tpx) in
        eval_h h env w $. fun h v ->
        cont h (Some (v, t))
    in
    match s with
      NonpureStmt (l, allowed, s) ->
      if allowed then
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes false leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont
      else
        static_error l "Non-pure statements are not allowed here."
    | CallStmt (l, "produce_limits", [], [Var (lv, x, _) as e],Static) ->
      if not pure then static_error l "This function may be called only from a pure context.";
      if List.mem x ghostenv then static_error l "The argument for this call must be a non-ghost variable.";
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      assume_is_of_type l (ev w) tp (fun () -> cont h env)
    | ProduceLemmaFunctionPointerChunkStmt (l, x, body) ->
      if not pure then static_error l "This construct is not allowed in a non-pure context.";
      begin
        match try_assoc x funcmap with
          None -> static_error l "No such function."
        | Some (funenv, fterm, _, k, tparams, rt, ps, atomic, pre, pre_tenv, post, functype_opt, _,fb,v) ->
          if k <> Lemma then static_error l "Not a lemma function.";
          begin
            match leminfo with
              None -> ()
            | Some (lems, g0, indinfo) ->
              if not (List.mem x lems) then static_error l "Function pointer chunks can only be produced for preceding lemmas.";
              if body = None then static_error l "produce_lemma_function_pointer_chunk statement must have a body."
          end;
          let ftn =
            match functype_opt with
              None -> static_error l "Function does not implement a function type."
            | Some (ftn, ftargs) -> ftn
          in
          let (_, _, _, _, symb, _) = List.assoc ("is_" ^ ftn) predfammap in
          let Some funcsym = fterm in
          let h = Chunk ((symb, true), [], real_unit, [funcsym], None)::h in
          match body with
            None -> cont h env
          | Some s ->
            let consume_chunk h cont =
              with_context (Executing (h, [], l, "Consuming lemma function pointer chunk")) $. fun () ->
              assert_chunk rules (pn,ilist) h ghostenv [] [] l (symb, true) [] real_unit dummypat (Some 1) [TermPat funcsym] (fun h coef ts chunk_size ghostenv env env' ->
                if not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk permission required.";
                cont h
              )
            in
            let lblenv =
              List.map
                begin fun (lbl, cont) ->
                  (lbl,
                   fun blocks_done sizemap tenv ghostenv h env ->
                   consume_chunk h (fun h -> cont blocks_done sizemap tenv ghostenv h env)
                  )
                end
                lblenv
            in
            let tcont _ _ _ h env =
              consume_chunk h (fun h ->
                tcont sizemap tenv ghostenv h env
              )
            in
            let return_cont h retval =
              consume_chunk h (fun h -> return_cont h retval)
            in
            verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont
      end
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) ->
      begin match try_assoc ftn functypemap with
        None -> static_error l "No such function type"
      | Some (lft, gh, rt, ftxmap, xmap, pre, post) ->
        if gh <> Real || ftxmap = [] then static_error l "A produce_function_pointer_chunk statement may be used only for parameterized function types.";
        let (lfn, fn) =
          match fpe with
            Var (lfn, x, _) -> (lfn, x)
          | _ -> static_error (expr_loc fpe) "Function name expected"
        in
        let (fterm, l1, rt1, xmap1, pre1, post1) =
          match try_assoc fn funcmap with
            None -> static_error lfn "Function name expected"
          | Some (fenv, Some fterm, l, k, tparams, rt, xmap, atomic, pre, pre_tenv, post, functype_opt, body', binding, visibility) ->
            if k <> Regular then static_error lfn "Regular function expected";
            if body' = None then register_prototype_used l fn;
            (fterm, l, rt, xmap, pre, post)
        in
        begin match (rt, rt1) with
          (None, _) -> ()
        | (Some t, Some t1) -> expect_type_core (pn,ilist) l "Function return type: " t1 t
        | _ -> static_error l "Return type mismatch: Function does not return a value"
        end;
        begin match zip xmap xmap1 with
          None -> static_error l "Function type parameter count does not match function parameter count"
        | Some bs ->
          List.iter
            begin fun ((x, tp), (x1, tp1)) ->
              expect_type_core (pn,ilist) l (Printf.sprintf "The types of function parameter '%s' and function type parameter '%s' do not match: " x1 x) tp tp1
            end
            bs
        end;
        let ftargenv =
          match zip ftxmap args with
            None -> static_error l "Incorrect number of function pointer chunk arguments"
          | Some bs ->
            List.map
              begin fun ((x, tp), e) ->
                let w = check_expr_t (pn,ilist) tparams tenv e tp in
                (x, ev w)
              end
              bs
        in
        let fparams =
          match zip params xmap with
            None -> static_error l "Incorrect number of parameter names"
          | Some bs ->
            List.map
              begin fun ((lx, x), (x0, tp)) ->
                if List.mem_assoc x tenv then static_error lx "Parameter name hides existing local variable";
                (x, x0, tp, get_unique_var_symb x tp)
              end
              bs
        in
        let (ss_before, callLoc, resultvar, ss_after) =
          let rec iter ss_before ss_after =
            match ss_after with
              [] -> static_error l "'call();' statement expected"
            | CallStmt (lc, "call", [], [], Static)::ss_after -> (List.rev ss_before, lc, None, ss_after)
            | DeclStmt (ld, te, x, CallExpr (lc, "call", [], [], [], Static))::ss_after ->
              if List.mem_assoc x tenv then static_error ld "Variable hides existing variable";
              let t = check_pure_type (pn,ilist) tparams te in
              begin match rt1 with
                None -> static_error ld "Function does not return a value"
              | Some rt1 ->
                expect_type (pn,ilist) ld rt1 t;
                (List.rev ss_before, lc, Some (x, t), ss_after)
              end
            | s::ss_after -> iter (s::ss_before) ss_after
          in
          iter [] ss
        in
        let cont () =
          let coef = get_dummy_frac_term () in
          let (_, _, _, _, symb, _) = List.assoc ("is_" ^ ftn) predfammap in
          cont (Chunk ((symb, true), [], coef, fterm::List.map snd ftargenv, None)::h) env
        in
        begin
          let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
          let h = [] in
          with_context (Executing (h, [], openBraceLoc, "Producing function type precondition")) $. fun () ->
          with_context PushSubcontext $. fun () ->
          let pre_env = [("this", fterm)] @ currentThreadEnv @ ftargenv @ List.map (fun (x, x0, tp, t) -> (x0, t)) fparams in
          assume_pred [] ("",[]) h [] pre_env pre real_unit None None $. fun h _ ft_env ->
          with_context PopSubcontext $. fun () ->
          let tenv = List.map (fun (x, x0, tp, t) -> (x, tp)) fparams @ tenv in
          let ghostenv = List.map (fun (x, x0, tp, t) -> x) fparams @ ghostenv in
          let env = List.map (fun (x, x0, tp, t) -> (x, t)) fparams @ env in
          let lblenv = [] in
          let pure = true in
          let return_cont h t = assert_false h [] l "You cannot return out of a produce_function_pointer_chunk statement" in
          begin fun tcont ->
            verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss_before tcont return_cont
          end $. fun sizemap tenv ghostenv h env ->
          with_context (Executing (h, env, callLoc, "Verifying function call")) $. fun () ->
          with_context PushSubcontext $. fun () ->
          let pre1_env = currentThreadEnv @ List.map (fun (x, x0, tp, t) -> (x0, t)) fparams in
          assert_pred rules [] ("",[]) h [] pre1_env pre1 true real_unit $. fun h _ f_env _ ->
          let (f_env, ft_env, tenv, ghostenv, env) =
            match rt1 with
              None -> (f_env, ft_env, tenv, ghostenv, env)
            | Some rt1 ->
              let result = get_unique_var_symb "result" rt1 in
              let f_env = ("result", result)::f_env in
              let ft_env =
                match rt with
                  None -> ft_env
                | Some rt -> ("result", result)::ft_env
              in
              let (tenv, ghostenv, env) =
                match resultvar with
                  None -> (tenv, ghostenv, env)
                | Some (x, t) ->
                  ((x, t)::tenv, x::ghostenv, (x, result)::env)
              in
              (f_env, ft_env, tenv, ghostenv, env)
          in
          assume_pred [] ("",[]) h [] f_env post1 real_unit None None $. fun h _ _ ->
          with_context PopSubcontext $. fun () ->
          begin fun tcont ->
            verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss_after tcont return_cont
          end $. fun sizemap tenv ghostenv h env ->
          with_context (Executing (h, env, closeBraceLoc, "Consuming function type postcondition")) $. fun () ->
          with_context PushSubcontext $. fun () ->
          assert_pred rules [] ("",[]) h [] ft_env post true real_unit $. fun h _ _ _ ->
          with_context PopSubcontext $. fun () ->
          check_leaks h [] closeBraceLoc "produce_function_pointer_chunk body leaks heap chunks"
        end;
        cont()
      end
    | CallStmt (l, "close_struct", targs, args, Static) when language = CLang ->
      let e = match (targs, args) with ([], [e]) -> e | _ -> static_error l "close_struct expects no type arguments and one argument." in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of close_struct must be of type pointer-to-struct." in
      let (_, fds_opt, padding_predsymb_opt) = List.assoc sn structmap in
      let fds = match fds_opt with Some fds -> fds | None -> static_error l "Cannot close a struct that does not declare a body." in
      let padding_predsymb = match padding_predsymb_opt with Some s -> s | None -> static_error l "Cannot close a struct that declares ghost fields." in
      eval_h h env e $. fun h pointerTerm ->
      with_context (Executing (h, env, l, "Consuming character array")) $. fun () ->
      let (_, _, _, _, chars_symb, _) = List.assoc ("chars") predfammap in
      assert_chunk rules (pn,ilist) h ghostenv [] [] l (chars_symb, true) [] real_unit dummypat None [TermPat pointerTerm; SrcPat DummyPat] $. fun h coef ts _ _ _ _ ->
      if not (definitely_equal coef real_unit) then assert_false h env l "Closing a struct requires full permission to the character array.";
      let [_; cs] = ts in
      with_context (Executing (h, env, l, "Checking character array length")) $. fun () ->
      let Some (_, _, _, _, length_symb) = try_assoc' (pn,ilist) "length" purefuncmap in
      if not (definitely_equal (ctxt#mk_app length_symb [cs]) (List.assoc sn struct_sizes)) then
        assert_false h env l "Could not prove that length of character array equals size of struct.";
      let rec iter h fds =
        match fds with
          [] ->
          cont (h @ [Chunk ((padding_predsymb, true), [], real_unit, [pointerTerm], None)]) env
        | (f, (lf, gh, t))::fds ->
          let fref = new fieldref f in
          fref#set_parent sn; fref#set_range t; assume_field h fref pointerTerm (get_unique_var_symb "value" t) real_unit (fun h -> iter h fds)
      in
      iter h fds
    | CallStmt (l, "open_struct", targs, args, Static) when language = CLang ->
      let e = match (targs, args) with ([], [e]) -> e | _ -> static_error l "open_struct expects no type arguments and one argument." in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of open_struct must be of type pointer-to-struct." in
      let (_, fds_opt, padding_predsymb_opt) = List.assoc sn structmap in
      let fds = match fds_opt with Some fds -> fds | None -> static_error l "Cannot open a struct that does not declare a body." in
      let padding_predsymb = match padding_predsymb_opt with Some s -> s | None -> static_error l "Cannot open a struct that declares ghost fields." in
      eval_h h env e $. fun h pointerTerm ->
      begin fun cont ->
        let rec iter h fds =
          match fds with
            [] -> cont h
          | (f, (_, gh, t))::fds ->
            let fref = new fieldref f in
            fref#set_parent sn;
            get_field (pn,ilist) h pointerTerm fref l $. fun h coef _ ->
            if not (definitely_equal coef real_unit) then assert_false h env l "Opening a struct requires full field chunk permissions.";
            iter h fds
        in
        iter h fds
      end $. fun h ->
      with_context (Executing (h, env, l, "Consuming struct padding chunk")) $. fun () ->
      assert_chunk rules (pn,ilist) h ghostenv [] [] l (padding_predsymb, true) [] real_unit dummypat None [TermPat pointerTerm] $. fun h coef _ _ _ _ _ ->
      if not (definitely_equal coef real_unit) then assert_false h env l "Opening a struct requires full permission to the struct padding chunk.";
      let (_, _, _, _, chars_symb, _) = List.assoc ("chars") predfammap in
      let cs = get_unique_var_symb "cs" (InductiveType ("list", [Char])) in
      let Some (_, _, _, _, length_symb) = try_assoc' (pn,ilist) "length" purefuncmap in
      assume (ctxt#mk_eq (ctxt#mk_app length_symb [cs]) (List.assoc sn struct_sizes)) $. fun () ->
      cont (Chunk ((chars_symb, true), [], real_unit, [pointerTerm], None)::h) env
    | CallStmt (l, "free", [], args,Static) ->
      begin
        match List.map (check_expr (pn,ilist) tparams tenv) args with
          [(arg, PtrType (StructType tn))] ->
          let _ = if pure then static_error l "Cannot call a non-pure function from a pure context." in
          let fds =
            match List.assoc tn structmap with
              (ls, Some fmap, _) -> fmap
            | _ -> static_error l "Freeing an object of a struct type declared without a body is not supported."
          in
          let arg = ev arg in
          let rec iter h fds =
            match fds with
              [] -> cont h env
            | (f, (lf, gh, t))::fds ->
              let fref = new fieldref f in
              fref#set_parent tn;
              get_field (pn,ilist) h arg fref l (fun h coef _ -> if not (definitely_equal coef real_unit) then assert_false h env l "Free requires full field chunk permissions."; iter h fds)
          in
          let (_, (_, _, _, _, malloc_block_symb, _)) = (List.assoc tn malloc_block_pred_map)in
          assert_chunk rules (pn,ilist)  h [] [] [] l (malloc_block_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat arg] (fun h coef _ _ _ _ _ ->
            iter h fds
          )
        | _ -> call_stmt l None "free" [] (List.map (fun e -> LitPat e) args) Static (fun h _ -> cont h env)
      end
    | CallStmt (l, "open_module", [], args, Static) ->
      if args <> [] then static_error l "open_module requires no arguments.";
      let (_, _, _, _, module_symb, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
      assert_chunk rules (pn,ilist) h [] [] [] l (module_symb, true) [] real_unit (SrcPat DummyPat) (Some 2) [TermPat current_module_term; TermPat ctxt#mk_true] $. fun h coef _ _ _ _ _ ->
      let globalChunks =
        List.map (fun (x, (l, tp, global_symb)) -> Chunk ((pointee_pred_symb l tp, true), [], coef, [global_symb; ctxt#mk_intlit 0], None)) globalmap
      in
      let codeChunks =
        if unloadable then [Chunk ((module_code_symb, true), [], coef, [current_module_term], None)] else []
      in
      cont (codeChunks @ globalChunks @ h) env
    | CallStmt (l, "close_module", [], args, Static) ->
      if args <> [] then static_error l "close_module requires no arguments.";
      let (_, _, _, _, module_symb, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
      begin fun cont ->
        let rec iter h globals =
          match globals with
            [] -> cont h
          | (x, (lg, tp, global_symb))::globals ->
            assert_chunk rules (pn,ilist) h [] [] [] l (pointee_pred_symb l tp, true) [] real_unit real_unit_pat (Some 1) [TermPat global_symb; SrcPat DummyPat] $. fun h _ _ _ _ _ _ ->
            iter h globals
        in
        iter h globalmap
      end $. fun h ->
      begin fun cont ->
        if unloadable then
          assert_chunk rules (pn,ilist) h [] [] [] l (module_code_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat current_module_term] $. fun h _ _ _ _ _ _ ->
          cont h
        else
          cont h
      end $. fun h ->
      cont (Chunk ((module_symb, true), [], real_unit, [current_module_term; ctxt#mk_false], None)::h) env
    | Assign (l, x, e) ->
      let (tpx, symb) = vartp l x in
      verify_expr (Some tpx) (Some x) e $. fun h (Some (v, _)) ->
      check_assign l x;
      update_local_or_global h env tpx x symb v cont
    | DeclStmt (l, te, x, e) ->
      if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.");
      let t = check_pure_type (pn,ilist) tparams te in
      let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap ((x, t)::tenv) ghostenv h env (Assign (l, x, e)) tcont return_cont (* BUGBUG: e should be typechecked outside of the scope of x *)
      ;
    | Write (l, e, f, rhs) ->
      let (w, tp) = check_deref true pure (pn,ilist) l tparams tenv e f in
      let wrhs = check_expr_t (pn,ilist) tparams tenv rhs tp in
      eval_h h env w (fun h t ->
        let (_, (_, _, _, _, f_symb, _)) = List.assoc (f#parent, f#name) field_pred_map in
        get_field (pn,ilist) h t f l (fun h coef _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a field requires full field permission.";
          cont (Chunk ((f_symb, true), [], real_unit, [t; ev wrhs], None)::h) env)
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
          cont (Chunk ((predSymb, true), [], real_unit, [t; ev wrhs], None)::h) env)
      )
    | CallStmt (l, g, targs, es,fb) ->
      call_stmt l None g targs (List.map (fun e -> LitPat e) es) fb (fun h _ -> cont h env)
    | IfStmt (l, e, ss1, ss2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (eval_h h env w ( fun h w ->
        branch
          (fun _ -> assume w (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss1 tcont return_cont))
          (fun _ -> assume (ctxt#mk_not w) (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss2 tcont return_cont))
      ))
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
                  match unfold_inferred_type tp with
                    TypeParam x -> convert_provertype term (provertype_of_type tp') ProverInductive
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
            (fun _ -> assume_eq t (ctxt#mk_app ctorsym xterms) (fun _ -> verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap (ptenv @ tenv) (pats @ ghostenv) h (xenv @ env) ss tcont return_cont))
            (fun _ -> iter (List.filter (function cn' -> cn' <> cn) ctors) cs)
      in
      iter (List.map (function (cn, _) -> cn) ctormap) cs
    | Assert (l, p) ->
      let (wp, tenv, _) = check_pred_core (pn,ilist) tparams tenv p in
      assert_pred rules [] (pn,ilist) h ghostenv env wp false real_unit (fun _ ghostenv env _ ->
        tcont sizemap tenv ghostenv h env
      )
    | Leak (l, p) ->
      let (wp, tenv, _) = check_pred_core (pn,ilist) tparams tenv p in
      assert_pred rules [] (pn,ilist) h ghostenv env wp false real_unit (fun h ghostenv env size ->
        let coef = get_dummy_frac_term () in
        assume_pred [] (pn,ilist) h ghostenv env wp coef None None (fun h _ _ ->
          tcont sizemap tenv ghostenv h env
        )
      )
    | Open (l, g, targs, pats0, pats, coefpat) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, tpenv, g_symb, pats0, dropcount, ps, env0, p, inputParamCount) =
        match resolve (pn,ilist) l g predfammap with
          Some (g, (_, _, _, _, g_symb, inputParamCount)) ->
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x))-> (l,x) | _ -> static_error l "Predicate family indices must be class names.") pats0)
          | _ -> List.map (function LitPat (Var (l, x, _)) -> x | _ -> static_error l "Predicate family indices must be function names.") pats0
          in
          begin
            let index_term fn =
              match file_type path with
                Java-> List.assoc fn classterms
              | _ -> funcnameterm_of funcmap fn
            in
            match try_assoc (g, fns) predinstmap with
              Some (predenv, _, predinst_tparams, ps, _, p) ->
              let (targs, tpenv) =
                let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predinst_tparams else targs in
                match zip predinst_tparams targs with
                  None -> static_error l (Printf.sprintf "Predicate expects %d type arguments." (List.length predinst_tparams))
                | Some bs -> (targs, bs)
              in
              let ps = List.map (fun (x, t) -> (x, t, instantiate_type tpenv t)) ps in
              let inputParamCount = match inputParamCount with None -> None | Some n -> Some (List.length fns + n) in
              (targs, tpenv, (g_symb, true), List.map (fun fn -> TermPat (index_term fn)) fns, List.length fns, ps, predenv, p, inputParamCount)
            | None -> static_error l "No such predicate instance."
          end
        | None ->
          begin
          match try_assoc' (pn,ilist) g predctormap with
            None -> static_error l "No such predicate or predicate constructor."
          | Some (_, ps1, ps2, body, funcsym) ->
            if targs <> [] then static_error l "Predicate constructor expects 0 type arguments.";
            let bs0 =
              match zip pats0 ps1 with
                None -> static_error l "Incorrect number of predicate constructor arguments."
              | Some bs ->
                List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions.") bs
            in
            let g_symb = ctxt#mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
            let ps2 = List.map (fun (x, t) -> (x, t, t)) ps2 in
            ([], [], (g_symb, false), [], 0, ps2, bs0, body, None)
          end
      in
      let (coefpat, tenv) =
        match coefpat with
          None -> (DummyPat, tenv)
        | Some coefpat -> check_pat (pn,ilist) l tparams tenv RealType coefpat
      in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv (List.map (fun (x, t0, t) -> t) ps) pats in
      let pats = pats0 @ srcpats wpats in
      assert_chunk rules (pn,ilist) h ghostenv env [] l g_symb targs real_unit (SrcPat coefpat) inputParamCount pats (fun h coef ts chunk_size ghostenv env [] ->
        let ts = drop dropcount ts in
        let env' =
          List.map
            begin fun ((p, tp0, tp), t) ->
             (p, prover_convert_term t tp tp0)
            end
            (let Some bs = zip ps ts in bs)
        in
        let env' = env0 @ env' in
        let body_size = match chunk_size with None -> None | Some k -> Some (k - 1) in
        with_context PushSubcontext (fun () ->
          assume_pred tpenv (pn,ilist) h ghostenv env' p coef body_size body_size (fun h _ _ ->
            with_context PopSubcontext (fun () -> tcont sizemap tenv' ghostenv h env)
          )
        )
      )
    | SplitFractionStmt (l, p, targs, pats, coefopt) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, g_symb, pts, inputParamCount) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate."
        | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount) ->
          let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predfam_tparams else targs in
          let tpenv =
            match zip predfam_tparams targs with
              None -> static_error l "Incorrect number of type arguments."
            | Some bs -> bs
          in
          if arity <> 0 then static_error l "Predicate families are not supported in split_fraction statements.";
          (targs, (g_symb, true), instantiate_types tpenv pts, inputParamCount)
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
      assert_chunk rules (pn,ilist) h ghostenv env [] l g_symb targs real_unit dummypat inputParamCount (srcpats wpats) (fun h coef ts chunk_size ghostenv env [] ->
        let coef1 = ctxt#mk_real_mul splitcoef coef in
        let coef2 = ctxt#mk_real_mul (ctxt#mk_real_sub real_unit splitcoef) coef in
        let h = Chunk (g_symb, targs, coef1, ts, None)::Chunk (g_symb, targs, coef2, ts, None)::h in
        tcont sizemap tenv' ghostenv h env
      )
    | MergeFractionsStmt (l, p, targs, pats) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, g_symb, pts, inputParamCount) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate."
        | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount) ->
          let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predfam_tparams else targs in
          let tpenv =
            match zip predfam_tparams targs with
              None -> static_error l "Incorrect number of type arguments."
            | Some bs -> bs
          in
          if arity <> 0 then static_error l "Predicate families are not supported in merge_fractions statements.";
          begin
            match inputParamCount with
              None ->
              static_error l
                ("Cannot merge this predicate: it is not declared precise. "
                 ^ "To declare a predicate precise, separate the input parameters "
                 ^ "from the output parameters using a semicolon in the predicate declaration.");
            | Some n -> (targs, (g_symb, true), instantiate_types tpenv pts, n)
          end
      in
      let (pats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      let (inpats, outpats) = take_drop inputParamCount pats in
      List.iter (function (LitPat e) -> () | _ -> static_error l "No patterns allowed at input positions.") inpats;
      let pats = srcpats pats in
      assert_chunk rules (pn,ilist) h ghostenv env [] l g_symb targs real_unit dummypat (Some inputParamCount) pats (fun h coef1 ts1 _ ghostenv env [] ->
        assert_chunk rules (pn,ilist) h ghostenv env [] l g_symb targs real_unit dummypat (Some inputParamCount) pats (fun h coef2 ts2 _ _ _ [] ->
          let (Some tpairs) = zip ts1 ts2 in
          let (ints, outts) = take_drop inputParamCount tpairs in
          let merged_chunk = Chunk (g_symb, targs, ctxt#mk_real_add coef1 coef2, ts1, None) in
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
      let Some (_, _, _, pts, g_symb, _) = try_assoc' (pn,ilist) bcn predfammap in
      let (pats, tenv) = check_pats (pn,ilist) l tparams tenv pts pats in
      assert_chunk rules (pn,ilist) h ghostenv env [] l (g_symb, true) [] real_unit dummypat None (srcpats pats) $. fun h coef ts _ ghostenv env [] ->
      if not (definitely_equal coef real_unit) then static_error l "Disposing a box requires full permission.";
      let boxId::argts = ts in
      let Some boxArgMap = zip boxpmap argts in
      let boxArgMap = List.map (fun ((x, _), t) -> (x, t)) boxArgMap in
      with_context PushSubcontext $. fun () ->
      assume_pred [] (pn,ilist) h ghostenv boxArgMap inv real_unit None None $. fun h _ boxVarMap ->
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
              let wpats = srcpats wpats in
              let Some (_, _, _, _, hpn_symb, _) = try_assoc' (pn,ilist) hpn predfammap in
              let handlePat::argPats = wpats in
              let pats = handlePat::TermPat boxId::argPats in
              assert_chunk rules (pn,ilist) h ghostenv env [] l (hpn_symb, true) [] real_unit dummypat None pats $. fun h coef ts _ ghostenv env [] ->
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
    | Close (l, g, targs, pats0, pats, coef) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (lpred, targs, tpenv, ps, bs0, g_symb, p, ts0) =
        match resolve (pn,ilist) l g predfammap with
          Some (g, (lpred, _, _, _, g_symb, inputParamCount)) ->
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x)) -> (l, x) | _ -> static_error l "Predicate family indices must be class names.") pats0)
          | _ -> List.map (function LitPat (Var (l, x, _)) -> x | _ -> static_error l "Predicate family indices must be function names.") pats0
          in
          begin
          match try_assoc (g, fns) predinstmap with
            Some (predenv, l, predinst_tparams, ps, inputParamCount, body) ->
            let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predinst_tparams else targs in
            let tpenv =
              match zip predinst_tparams targs with
                None -> static_error l "Incorrect number of type arguments."
              | Some bs -> bs
            in
            let ts0 = match file_type path with
              Java -> List.map (fun cn -> List.assoc cn classterms) fns
            | _ -> List.map (fun fn -> funcnameterm_of funcmap fn) fns
            in
            (lpred, targs, tpenv, ps, predenv, (g_symb, true), body, ts0)
          | None -> static_error l "No such predicate instance."
          end
        | None ->
          begin
            match try_assoc' (pn,ilist) g predctormap with
              None -> static_error l ("No such predicate family instance or predicate constructor: "^g)
            | Some (lpred, ps1, ps2, body, funcsym) ->
              let bs0 =
                match zip pats0 ps1 with
                  None -> static_error l "Incorrect number of predicate constructor arguments."
                | Some bs ->
                  List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions.") bs
              in
              let g_symb = ctxt#mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
              if targs <> [] then static_error l "Incorrect number of type arguments.";
              (lpred, [], [], ps2, bs0, (g_symb, false), body, [])
          end
      in
      let ps =
        match zip pats ps with
          None -> static_error l "Wrong number of arguments."
        | Some bs ->
          List.map
            begin fun (pat, (p, tp0)) ->
              let tp = instantiate_type tpenv tp0 in
              let t =
                match pat with
                  LitPat e -> Some (ev (check_expr_t (pn,ilist) tparams tenv e tp))
                | _ -> None
              in
              (p, pat, tp0, tp, t)
            end
            bs
      in
      let coef =
        match coef with
          None -> real_unit
        | Some (LitPat coef) -> let coef = check_expr_t (pn,ilist) tparams tenv coef RealType in ev coef
        | _ -> static_error l "Coefficient in close statement must be expression."
      in
      let env' = flatmap (function (p, pat, tp0, tp, Some t) -> [(p, prover_convert_term t tp tp0)] | _ -> []) ps in
      let env' = bs0 @ env' in
      with_context PushSubcontext (fun () ->
        assert_pred rules tpenv (pn,ilist) h ghostenv env' p true coef (fun h p_ghostenv p_env size_first ->
          with_context (Executing (h, p_env, lpred, "Inferring chunk arguments")) $. fun () ->
          let ts =
            List.map
              begin fun (p, pat, tp0, tp, t) ->
                match t with
                  Some t -> ([], t)
                | None ->
                  let t =
                    match try_assoc p p_env with
                      None -> assert_false h p_env l (Printf.sprintf "Predicate body does not bind parameter '%s'; it must be supplied in the close statement." p)
                    | Some t -> prover_convert_term t tp0 tp
                  in
                  let env =
                    match pat with
                      VarPat x -> [x, t]
                    | _ -> []
                  in
                  (env, t)
              end
              ps
          in
          with_context PopSubcontext $. fun () ->
          with_context (Executing (h, env, l, "Producing predicate chunk")) $. fun () ->
          let env = List.fold_left (fun env0 (env, t) -> merge_tenvs l env env0) env ts in
          let ts = List.map (fun (env, t) -> t) ts in
          cont (Chunk (g_symb, targs, coef, ts0 @ ts, None)::h) env
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
      assert_pred rules [] (pn,ilist) h ghostenv boxArgMap inv true real_unit $. fun h _ boxVarMap _ ->
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
              let (_, _, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with 
                None-> static_error l ("No such predicate family: "^hpn)
              | Some x -> x
              in
              iter (Chunk ((hpn_symb, true), [], real_unit, handleIdTerm::boxIdTerm::List.map (fun (x, t) -> t) hpArgMap, None)::handleChunks) handleClauses
            end
          | [] -> cont handleChunks
        in
        iter [] handleClauses
      end $. fun handleChunks ->
      let (_, _, _, _, bcn_symb, _) = match try_assoc' (pn,ilist) bcn predfammap with
        None -> static_error l ("No such predicate family: "^bcn)
      | Some x-> x
      in
      with_context PopSubcontext $. fun () ->
      tcont sizemap ((x, BoxIdType)::tenv) (x::ghostenv) (Chunk ((bcn_symb, true), [], real_unit, boxIdTerm::boxArgs, None)::(handleChunks@h)) ((x, boxIdTerm)::env)
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
      let (_, _, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with
        None -> static_error l ("No such predicate family: "^hpn)
      | Some x-> x
      in
      tcont sizemap ((x, HandleIdType)::tenv) (x::ghostenv) (Chunk ((hpn_symb, true), [], real_unit, [handleTerm; boxIdTerm], None)::h) ((x, handleTerm)::env)
    | ReturnStmt (l, eo) ->
      verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env l eo [] return_cont
    | WhileStmt (l, e, p, ss, closeBraceLoc) ->
      let _ = if pure then static_error l "Loops are not yet supported in a pure context." in
      let p = match p with None -> static_error l "Loop invariant required." | Some p -> p in
      let e = check_expr_t (pn,ilist) tparams tenv e boolt in
      check_ghost ghostenv l e;
      let xs = block_assigned_variables ss in
      let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
      let (p, tenv') = check_pred (pn,ilist) tparams tenv p in
      assert_pred rules [] (pn,ilist) h ghostenv env p true real_unit (fun h _ _ _ ->
        let bs = List.map (fun x -> (x, get_unique_var_symb x (List.assoc x tenv))) xs in
        let env = bs @ env in
        branch
          (fun _ ->
             assume_pred [] (pn,ilist) [] ghostenv env p real_unit None None (fun h' ghostenv' env' ->
               (eval_h h' env e (fun h' v -> assume (v) (fun _ ->
                 let lblenv =
                   List.map
                     begin fun (lbl, cont) ->
                       (lbl, fun blocks_done sizemap tenv ghostenv h'' env -> cont blocks_done sizemap tenv ghostenv (h'' @ h) env)
                     end
                     lblenv
                 in
                 verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv' ghostenv' h' env' ss (fun _ _ _ h'' env ->
                   let env = List.filter (fun (x, _) -> List.mem_assoc x tenv) env in
                   assert_pred rules [] (pn,ilist) h'' ghostenv env p true real_unit (fun h''' _ _ _ ->
                     check_leaks h''' env closeBraceLoc "Loop leaks heap chunks."
                   )
                 ) (fun h'' retval -> return_cont (h'' @ h) retval)
               )))
             )
          )
          (fun _ ->
             assume_pred [] (pn,ilist) h ghostenv env p real_unit None None (fun h ghostenv' env' ->
               (eval_h h env e (fun h v -> assume (ctxt#mk_not (v)) (fun _ ->
                 tcont sizemap tenv' ghostenv' h env')))))
      )
    | Throw (l, e) ->
      if pure then static_error l "Throw statements are not allowed in a pure context.";
      let e = check_expr_t (pn,ilist) tparams tenv e (ObjType "java.lang.Object") in
      check_ghost ghostenv l e;
      ()
    | TryCatch (l, body, catches) ->
      if pure then static_error l "Try-catch statements are not allowed in a pure context.";
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      branch
        begin fun () ->
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont
        end
        begin fun () ->
          (* Havoc the variables that are assigned by the try block. *)
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb x (List.assoc x tenv))) xs in
          let env = bs @ env in
          let h = [] in
          let rec iter catches =
            match catches with
              [] -> ()
            | (l, te, x, body)::catches ->
              branch
                begin fun () ->
                  if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.");
                  let t = check_pure_type (pn,ilist) tparams te in
                  let xterm = get_unique_var_symb x t in
                  let tenv = (x, t)::tenv in
                  let env = (x, xterm)::env in
                  verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont
                end
                begin fun () ->
                  iter catches
                end
          in
          iter catches
        end
    | TryFinally (l, body, lf, finally) ->
      if pure then static_error l "Try-finally statements are not allowed in a pure context.";
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (* Tricky stuff; I hope this is correct... *)
      branch
        begin fun () ->
          let lblenv =
            List.map
              begin fun (lbl, cont) ->
                let cont blocks_done sizemap tenv ghostenv h env =
                  let tcont _ _ _ h env = cont blocks_done sizemap tenv ghostenv h env in
                  verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont
                in
                (lbl, cont)
              end
              lblenv
          in
          let tcont _ _ _ h env =
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont
          in
          let return_cont h retval =
            let tcont _ _ _ h _ = return_cont h retval in
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont
          in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont
        end
        begin fun () ->
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb x (List.assoc x tenv))) xs in
          let env = bs @ env in
          let h = [] in
          let tcont _ _ _ _ _ = () in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont
        end
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
      let pre_bcp_pats = srcpats pre_bcp_pats in
      let (_, _, _, _, boxpred_symb, _) = match try_assoc' (pn,ilist) pre_bcn predfammap with 
        Some x->x
      | None -> static_error lcb ("Box predicate not found: "^pre_bcn)
      in
      assert_chunk rules (pn,ilist) h ghostenv env [] lcb (boxpred_symb, true) [] real_unit dummypat None pre_bcp_pats (fun h box_coef ts chunk_size ghostenv env [] ->
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
        let (_, _, _, _, pre_handlepred_symb, _) = match try_assoc' (pn,ilist) pre_hpn predfammap with 
          Some x->x
        | None -> static_error lcb ("Box predicate not found: "^pre_bcn)
        in
        let (pre_hp_pats, tenv) = check_pats (pn,ilist) lch tparams tenv (HandleIdType::List.map (fun (x, t) -> t) pre_handlePred_parammap) pre_hp_pats in
        let (pre_handleId_pat::pre_hpargs_pats) = srcpats pre_hp_pats in
        assert_chunk rules (pn,ilist) h ghostenv (("#boxId", boxId)::env) [] lch (pre_handlepred_symb, true) [] real_unit dummypat None (pre_handleId_pat::TermPat boxId::pre_hpargs_pats)
          (fun h coef ts chunk_size ghostenv env [] ->
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
             assume_pred [] (pn,ilist) h ghostenv pre_boxArgMap inv real_unit None None $. fun h _ pre_boxVarMap ->
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
                       | Some (funenv, fterm, l, k, tparams, rt, ps, atomic, pre, pre_tenv, post, functype_opt, body,fb,v) ->
                         if not atomic then static_error l "A non-pure statement in the body of an atomic perform_action statement must be a call of an atomic function."
                     end;
                     NonpureStmt (l, true, s)
                   | s -> s
                   end
                   ss
               in
               if atomic && !nonpureStmtCount <> 1 then static_error lpa "The body of an atomic perform_action statement must include exactly one non-pure statement.";
               verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env ->
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
                 assert_pred rules [] (pn,ilist) h ghostenv post_boxArgMap inv true real_unit $. fun h _ post_boxVarMap _ ->
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
                 let (_, _, _, _, post_handlePred_symb, _) = match try_assoc' (pn,ilist) post_hpn predfammap with 
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
                 let boxChunk = Chunk ((boxpred_symb, true), [], box_coef, boxId::List.map (fun (x, t) -> t) post_boxArgMap, None) in
                 let hpChunk = Chunk ((post_handlePred_symb, true), [], real_unit, handleId::boxId::List.map (fun (x, t) -> t) post_hpargs, None) in
                 let h = boxChunk::hpChunk::h in
                 with_context PopSubcontext $. fun () ->
                 tcont sizemap tenv ghostenv h env
               ) return_cont
             )
          )
      )
    | BlockStmt (l, ds, ss) ->
      let (lems, predinsts) =
        List.fold_left
          begin fun (lems, predinsts) decl ->
            match decl with
            | PredFamilyInstanceDecl (l, p, predinst_tparams, is, xs, body) ->
              let i = match is with [i] -> i | _ -> static_error l "Local predicate family declarations must declare exactly one index." in
              if List.mem_assoc (p, i) predinsts then static_error l "Duplicate predicate family instance.";
              (lems, ((p, i), (l, predinst_tparams, xs, body))::predinsts)
            | Func (l, Lemma, tparams, rt, fn, xs, atomic, functype_opt, contract_opt, Some body, Static, Public) ->
              if List.mem_assoc fn funcmap || List.mem_assoc fn lems then static_error l "Duplicate function name.";
              if List.mem_assoc fn tenv then static_error l "Local lemma name hides existing local variable name.";
              let fterm = get_unique_var_symb fn (PtrType Void) in
              ((fn, (fterm, l, tparams, rt, xs, atomic, functype_opt, contract_opt, body))::lems, predinsts)
            | _ -> static_error l "Local declarations must be lemmas or predicate family instances."
          end
          ([], [])
          ds
      in
      let (lems, predinsts) = (List.rev lems, List.rev predinsts) in
      let funcnameterms' =
        List.map
          (fun (fn, (fterm, l, tparams, rt, xs, atomic, functype_opt, contract_opt, body)) -> (fn, fterm))
        lems
      in
      let env = funcnameterms' @ env in
      let ghostenv = List.map (fun (fn, _) -> fn) funcnameterms' @ ghostenv in
      let tenv = List.map (fun (fn, _) -> (fn, PtrType Void)) funcnameterms' @ tenv in
      let predinstmap' =
        List.map
          begin fun ((p, (li, i)), (l, predinst_tparams, xs, body)) ->
            if not (List.mem_assoc i lems) then static_error li "Index of local predicate family instance must be lemma declared in same block.";
            check_predinst (pn, ilist) tparams tenv env l p predinst_tparams [i] xs body
          end
          predinsts
      in
      let funcmap' =
        List.map
          begin fun (fn, (fterm, l, tparams', rt, xs, atomic, functype_opt, contract_opt, body)) ->
            let (rt, xmap, pre, pre_tenv, post) =
              check_func_header pn ilist tparams tenv env l Lemma tparams' rt fn (Some fterm) xs atomic functype_opt contract_opt (Some body)
            in
            (fn, (env, Some fterm, l, Lemma, tparams', rt, xmap, atomic, pre, pre_tenv, post, functype_opt, Some (Some body), Static, Public))
          end
          lems
      in
      let predinstmap = predinstmap' @ predinstmap in
      let funcmap = funcmap' @ funcmap in
      let verify_lems lems0 =
        List.fold_left
          begin fun lems0 (fn, (funenv, fterm, l, k, tparams', rt, xmap, atomic, pre, pre_tenv, post, functype_opt, Some (Some (ss, closeBraceLoc)), _, _)) ->
            verify_func pn ilist lems0 boxes predinstmap funcmap tparams funenv l k tparams' rt fn xmap pre pre_tenv post ss closeBraceLoc
          end
          lems0
          funcmap'
      in
      let leminfo =
        match leminfo with
          None ->
          let lems0 =
            flatmap
              (function (fn, (funenv, fterm, l, Lemma, tparams, rt, ps, atomic, pre, pre_tenv, post, functype_opt, body, _, _)) -> [fn] | _ -> [])
              funcmap
          in
          verify_lems lems0;
          None
        | Some (lems, g, indinfo) ->
          Some (verify_lems lems, g, indinfo)
      in
      let cont h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env -> cont h env) return_cont
    | PureStmt (l, s) ->
      begin
        match s with
          PerformActionStmt (_, nonpure_ctxt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) ->
          nonpure_ctxt := not pure
        | _ -> ()
      end;
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont
    | GotoStmt (l, lbl) ->
      if pure then static_error l "goto statements are not allowed in a pure context";
      begin
        match try_assoc lbl lblenv with
          None -> static_error l "No such label."
        | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | NoopStmt l -> cont h env
    | LabelStmt (l, _) -> static_error l "Label statements cannot appear in this position."
    | InvariantStmt (l, _) -> static_error l "Invariant statements cannot appear in this position."
  and
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        let time0 = Sys.time() in
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          if verbose then printff "%s: %f seconds\n" (string_of_loc (stmt_loc s)) (Sys.time() -. time0);
          verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont
        ) return_cont
      )
  and
  
  (* Region: verification of blocks *)
  
    goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont block =
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
        assert_pred rules [] (pn,ilist) h ghostenv env inv true real_unit (fun h _ _ _ ->
          check_leaks h env l "Loop leaks heap chunks."
        )
      | (false, None) ->
        let blocks_done = block::blocks_done in
        verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont
    end
  and verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env l eo epilog return_cont =
    if pure && not (List.mem "#result" ghostenv) then static_error l "Cannot return from a regular function in a pure context.";
    begin fun cont ->
      match eo with
        None -> cont h None
      | Some e ->
        if not pure then check_ghost ghostenv l e;
        let tp = match try_assoc "#result" tenv with None -> static_error l "Void function cannot return a value: " | Some tp -> tp in
        let w = check_expr_t (pn,ilist) tparams tenv e tp in
        eval_h (pn,ilist) pure h env w $. fun h v ->
        cont h (Some v)
    end $. fun h retval ->
    begin fun cont ->
      if not pure && unloadable then
        let codeCoef = List.assoc "currentCodeFraction" env in
        let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
        assume_chunk h (module_code_symb, true) [] codeCoef (Some 1) [current_module_term] None cont
      else
        cont h
    end $. fun h ->
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env epilog cont (fun _ _ -> assert false)
    end $. fun sizemap tenv ghostenv h env ->
    return_cont h retval
  and
    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont =
    let (decls, ss) =
      let rec iter decls ss =
        match ss with
          (DeclStmt _) as s::ss -> iter (s::decls) ss
        | _ -> (List.rev decls, ss)
      in
      iter [] ss
    in
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env decls cont return_cont
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
            | block'::_ -> goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont block'
          in
          let block' = `Block (inv, ss, cont) in
          let lblenv =
            let cont blocks_done sizemap tenv ghostenv h env =
              goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont block'
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
      | block0::_ -> goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont block0
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
            assume_pred [] (pn,ilist) [] ghostenv env inv real_unit None None (fun h ghostenv env ->
              let blocks_done = block::blocks_done in
              verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont
            )
        end
        blocks
    end
  and verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont =
    let (ss, tcont) =
      if not pure && List.exists (function ReturnStmt (_, _) -> true | _ -> false) ss then
        let (ss, lr, eo, epilog) =
          let rec iter ss ss' =
            match ss' with
              ReturnStmt (lr, eo)::epilog -> (List.rev ss, lr, eo, epilog)
            | s::ss' -> iter (s::ss) ss'
          in
          iter [] ss
        in
        let tcont sizemap tenv ghostenv h env =
          let epilog = List.map (function (PureStmt (l, s)) -> s | s -> static_error (stmt_loc s) "An epilog statement must be a pure statement.") epilog in
          verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env lr eo epilog return_cont
        in
        (ss, tcont)
      else
        (ss, tcont)
    in
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont
  
  (* Region: verification of function bodies *)
  
  and verify_func pn ilist lems boxes predinstmap funcmap tparams env l k tparams' rt g ps pre pre_tenv post ss closeBraceLoc =
    let tparams = tparams' @ tparams in
    let _ = push() in
    let penv = get_unique_var_symbs ps in (* actual params invullen *)
    let (sizemap, indinfo) =
      match ss with
        [SwitchStmt (_, Var (_, x, _), _)] -> (
        match try_assoc x penv with
          None -> ([], None)
        | Some t -> ([(t, 0)], Some x)
        )
      | _ -> ([], None)
    in
    let tenv =
      match rt with
        None -> pre_tenv
      | Some rt -> ("#result", rt)::pre_tenv
    in
    let (in_pure_context, leminfo, lems', ghostenv) =
      if k = Lemma then 
        (true, Some (lems, g, indinfo), g::lems, List.map (function (p, t) -> p) ps @ ["#result"])
      else
        (false, None, lems, [])
    in
    let env = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] @ penv @ env in
    let _ =
      check_should_fail () $. fun _ ->
      assume_pred [] (pn, ilist) [] ghostenv env pre real_unit (Some 0) None (fun h ghostenv env ->
        let (prolog, ss) =
          if in_pure_context then
            ([], ss)
          else
            let rec iter prolog ss =
              match ss with
                PureStmt (l, s)::ss -> iter (s::prolog) ss
              | _ -> (List.rev prolog, ss)
            in
            iter [] ss
        in
        begin fun tcont ->
          verify_cont (pn,ilist) [] [] tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env prolog tcont (fun _ _ -> assert false)
        end $. fun sizemap tenv ghostenv h env ->
        begin fun cont ->
          if unloadable && not in_pure_context then
            let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
            with_context (Executing (h, env, l, "Consuming code fraction")) $. fun () ->
            assert_chunk rules (pn,ilist) h [] [] [] l (module_code_symb, true) [] real_unit (SrcPat DummyPat) (Some 1) [TermPat current_module_term] $. fun h coef _ _ _ _ _ ->
            let half = real_mul l real_half coef in
            cont (Chunk ((module_code_symb, true), [], half, [current_module_term], None)::h) (("currentCodeFraction", RealType)::tenv) ("currentCodeFraction"::ghostenv) (("currentCodeFraction", half)::env)
          else
            cont h tenv ghostenv env
        end $. fun h tenv ghostenv env ->
        let do_return h env_post =
          assert_pred rules [] (pn,ilist) h ghostenv env_post post true real_unit (fun h ghostenv env size_first ->
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
        begin fun tcont ->
          verify_block (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont
        end $. fun sizemap tenv ghostenv h env ->
        verify_return_stmt (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env closeBraceLoc None [] return_cont
      )
    in
    let _ = pop() in
    lems'
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
      | (xmap, (lm,pre,pre_tenv,post,ss,v))::rest ->
          match ss with
            None -> let (((_,p),_,_),((_,_),_,_))=lm in 
              if Filename.check_suffix p ".javaspec" then verify_cons (pn,ilist) cn boxes lems rest
              else static_error lm "Constructor specification is only allowed in javaspec files!"
          | Some(Some (ss, closeBraceLoc)) ->
              let _ = push() in
              let env = get_unique_var_symbs ([(current_thread_name, current_thread_type)] @ xmap) in
              let (sizemap, indinfo) = switch_stmt ss env in
              let (in_pure_context, leminfo, lems', ghostenv) = (false, None, lems, []) in
              let _ =
                assume_pred [] (pn,ilist) [] ghostenv env pre real_unit (Some 0) None
                (fun h ghostenv env ->
                  let do_body h ghostenv env=
                    let do_return h env_post = assert_pred rules [] (pn,ilist) h ghostenv env_post post true real_unit 
                    (fun h ghostenv env size_first ->(check_leaks h env closeBraceLoc "Function leaks heap chunks."))
                    in
                    let return_cont h retval =
                      match retval with None -> do_return h env | Some t -> do_return h (("this", t)::env)
                    in
                    let tenv = ("this", ObjType cn)::pre_tenv in
                    verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss 
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
                               (do_body h ghostenv env'')
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
      | (g, (l,rt, ps,pre,pre_tenv,post,sts,fb,v))::meths ->
        match sts with
          None -> let (((_,p),_,_),((_,_),_,_))=l in 
            if Filename.check_suffix p ".javaspec" then verify_meths (pn,ilist) boxes lems meths
            else static_error l "Constructor specification is only allowed in javaspec files!"
        | Some(Some (ss, closeBraceLoc)) ->(
            let _ = push() in
            let env = get_unique_var_symbs (ps @ [(current_thread_name, current_thread_type)]) in (* actual params invullen *)
            begin fun cont ->
              if fb = Instance then
              begin
                let ("this", thisTerm)::_ = env in
                let ("this", ObjType cn)::_ = ps in
                (* CAVEAT: Remove this assumption once we allow subclassing. *)
                (* assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) $. fun () -> *)
                cont (("this", ObjType cn)::pre_tenv)
              end else cont pre_tenv
            end $. fun tenv ->
            let (sizemap, indinfo) = switch_stmt ss env in
            let tenv = match rt with None ->tenv | Some rt -> ("#result", rt)::tenv in
            let (in_pure_context, leminfo, lems', ghostenv) =(false, None, lems, []) in
            let _ =
              assume_pred [] (pn,ilist) [] ghostenv env pre real_unit (Some 0) None (fun h ghostenv env ->
              let do_return h env_post = assert_pred rules [] (pn,ilist) h ghostenv env_post post true real_unit (fun h ghostenv env size_first ->(check_leaks h env closeBraceLoc "Function leaks heap chunks."))
              in
              let return_cont h retval =
                match (rt, retval) with
                  (None, None) -> do_return h env
                | (Some tp, Some t) -> do_return h (("result", t)::env)
                | (None, Some _) -> assert_false h env l "Void function returns a value."
                | (Some _, None) -> assert_false h env l "Non-void function does not return a value."
              in
              verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun _ _ _ h _ -> return_cont h None) return_cont
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
     [] -> (boxes, lems)
    | Func (l, Lemma, _, rt, g, ps, _, _, _, None, _, _)::ds -> let g=full_name pn g in
      verify_funcs (pn,ilist)  boxes (g::lems) ds
    | Func (_, k, _, _, g, _, _, functype_opt, _, Some _, _, _)::ds when k <> Fixpoint ->
      let g = full_name pn g in
      let ([], fterm, l, k, tparams', rt, ps, atomic, pre, pre_tenv, post, _, Some (Some (ss, closeBraceLoc)),fb,v) = (List.assoc g funcmap)in
      let tparams = [] in
      let env = [] in
      let lems' = verify_func pn ilist lems boxes predinstmap funcmap tparams env l k tparams' rt g ps pre pre_tenv post ss closeBraceLoc in
      verify_funcs (pn, ilist) boxes lems' ds
    | BoxClassDecl (l, bcn, _, _, _, _)::ds -> let bcn=full_name pn bcn in
      let (Some (l, boxpmap, boxinv, boxvarmap, amap, hpmap)) = try_assoc' (pn,ilist) bcn boxmap in
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
                    let currentThread = get_unique_var_symb "currentThread" IntType in
                    let actionHandle = get_unique_var_symb "actionHandle" HandleIdType in
                    let predicateHandle = get_unique_var_symb "predicateHandle" HandleIdType in
                    assume (ctxt#mk_not (ctxt#mk_eq actionHandle predicateHandle)) (fun () ->
                    let pre_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb ("old_" ^ x) t)) boxpmap in
                    with_context (Executing ([], [], l, "Checking preserved_by clause.")) $. fun () ->
                    with_context PushSubcontext $. fun () ->
                    assume_pred [] (pn,ilist) [] [] pre_boxargs boxinv real_unit None None $. fun _ _ pre_boxvars ->
                    let old_boxvars = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxvars in
                    let post_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) boxpmap in
                    assume_pred [] (pn,ilist) [] [] post_boxargs boxinv real_unit None None $. fun _ _ post_boxvars ->
                    with_context PopSubcontext $. fun () ->
                    let hpargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) pmap in
                    let aargs = List.map (fun (x, (y, t)) -> (x, y, get_unique_var_symb x t)) apbs in
                    let apre_env = List.map (fun (x, y, t) -> (y, t)) aargs in
                    let ghostenv = List.map (fun (x, t) -> x) tenv in
                    assume (eval (pn,ilist) None ([("actionHandle", actionHandle)] @ pre_boxvars @ apre_env) pre) (fun () ->
                      assume (eval (pn,ilist) None ([("predicateHandle", predicateHandle)] @ pre_boxvars @ hpargs) inv) (fun () ->
                        assume (eval (pn,ilist) None ([("actionHandle", actionHandle)] @ post_boxvars @ old_boxvars @ apre_env) post) (fun () ->
                          let aarg_env = List.map (fun (x, y, t) -> (x, t)) aargs in
                          let env = ["actionHandle", actionHandle; "predicateHandle", predicateHandle; "currentThread", currentThread] @
                            post_boxvars @ old_boxvars @ aarg_env @ hpargs in
                          verify_cont (pn,ilist) [] [] [] boxes true leminfo funcmap predinstmap [] tenv ghostenv [] env ss (fun _ _ _ _ _ ->
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
  let lems0 =
    flatmap
      (function (g, (funenv, fterm, l, Lemma, tparams, rt, ps, atomic, pre, pre_tenv, post, functype_opt, body, fb, v)) -> [g] | _ -> [])
      funcmap0
  in
  let rec verify_funcs' boxes lems ps=
    match ps with
      PackageDecl(l,pn,il,ds)::rest-> let (boxes, lems) = verify_funcs (pn,il) boxes lems ds in verify_funcs' boxes lems rest
    | [] -> verify_classes boxes lems classmap
  in
  verify_funcs' [] lems0 ps
  
  in
  
  ((!prototypes_used, prototypes_implemented, !functypes_implemented), (structmap1, enummap1, globalmap1, inductivemap1, purefuncmap1,predctormap1, fixpointmap1, malloc_block_pred_map1, field_pred_map1, predfammap1, predinstmap1, functypemap1, funcmap1, boxmap,classmap1,interfmap1))
  
  in
  
  (* Region: top-level stuff *)
  
  let main_file= ref ("",dummy_loc) in
  let jardeps= ref [] in
  let basepath=(Filename.basename path) in
  let dirpath= (Filename.dirname path) in
  let (prototypes_used, prototypes_implemented, functypes_implemented) =
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
        if Filename.check_suffix (Filename.basename path) ".h" then
          parse_header_file "" path reportRange reportShouldFail
        else
          parse_c_file path reportRange reportShouldFail
    in
    let result =
      check_should_fail ([], [], []) $. fun () ->
      let (linker_info, _) = check_file true programDir headers ds in
      linker_info
    in
    begin
      match !shouldFailLocs with
        [] -> ()
      | l::_ -> static_error l "No error found on line."
    end;
    result
  in
  
  stats#appendProverStats ctxt#stats;

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
      @
      List.sort compare
        begin
          List.map
            begin fun (fn, (((_, header), _, _), _), ftn, ftargs, unloadable) ->
              Printf.sprintf
                ".provides %s : %s#%s(%s)%s" fn header ftn (String.concat "," ftargs) (if unloadable then " unloadable" else "")
            end
            functypes_implemented
        end
      @
      [".produces module " ^ current_module_name]
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

(* Region: prover selection *)

let verify_program_with_stats ctxt print_stats verbose path reportRange breakpoint =
  do_finally
    (fun () -> verify_program_core ctxt verbose path reportRange breakpoint)
    (fun () -> if print_stats then stats#printStats)

class virtual prover_client =
  object
    method virtual run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit
  end

let prover_table: (string * (string * (prover_client -> unit))) list ref = ref []

let register_prover name banner f =
  prover_table := (name, (banner, f))::!prover_table

let prover_banners () = String.concat "" (List.map (fun (_, (banner, _)) -> banner) !prover_table)

let banner () =
  "Verifast " ^ Vfversion.version ^ " for C and Java (released " ^ Vfversion.release_date ^ ") <http://www.cs.kuleuven.be/~bartj/verifast/>\n" ^
  "By Bart Jacobs <http://www.cs.kuleuven.be/~bartj/>, Jan Smans <http://www.cs.kuleuven.be/~jans/>, and Frank Piessens, with contributions by Cedric Cuypers, Frederic Vogels, and Lieven Desmet" ^
  prover_banners ()

let lookup_prover prover =
  match prover with
    None ->
    begin
      match !prover_table with
        [] -> assert false
      | (_, (_, f))::_ -> f
    end
  | Some name ->
    begin
      match try_assoc name !prover_table with
        None -> failwith ("No such prover: " ^ name)
      | Some (banner, f) -> f
    end
      
let verify_program prover print_stats options path reportRange breakpoint =
  lookup_prover prover
    (object
       method run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit =
         fun ctxt -> verify_program_with_stats ctxt print_stats options path reportRange breakpoint
     end)

(* Region: linker *)

let remove_dups bs =
  let rec iter bs0 bs =
    match bs with
      [] -> List.rev bs0
    | (x, v)::bs ->
      if List.mem_assoc x bs0 then iter bs0 bs else iter ((x, v)::bs0) bs
  in
  iter [] bs

exception LinkError of string

let read_file_lines path msg =
  if Sys.file_exists path then
    let file = open_in path in
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
  else failwith msg

let parse_line line =
  let space = String.index line ' ' in
  let command = String.sub line 0 space in
  let symbol = String.sub line (space + 1) (String.length line - space - 1) in
  let n = String.length symbol in
  for i = 0 to n - 1 do if symbol.[i] = '/' then symbol.[i] <- '\\' done;
  let symbol = if startswith symbol ".\\" then String.sub symbol 2 (String.length symbol - 2) else symbol in
  (command, symbol)

let link_program isLibrary modulepaths emitDllManifest exports =
  let rec iter impls modulepaths =
    match modulepaths with
      [] -> impls
    | modulepath::modulepaths ->
      let manifest_path = Filename.chop_extension modulepath ^ ".vfmanifest" in
      let lines =
        if List.mem_assoc manifest_path !manifest_map then
          List.assoc manifest_path !manifest_map
        else
          read_file_lines manifest_path
            ("VeriFast link phase error: could not find .vfmanifest file '" ^ manifest_path ^ "' for module '" ^ modulepath ^ "'. Re-verify the module using the -emit_manifest option.")
      in
      let rec iter0 impls' lines =
        match lines with
          [] -> iter impls' modulepaths
        | line::lines ->
          let (command, symbol) = parse_line line in
          begin
            match command with
              ".requires" -> if List.mem symbol impls then iter0 impls' lines else raise (LinkError ("Module '" ^ modulepath ^ "': unsatisfied requirement '" ^ symbol ^ "'."))
            | ".provides" -> iter0 (symbol::impls') lines
            | ".produces" -> iter0 (symbol::impls') lines
          end
      in
      iter0 impls lines
  in
  let impls = iter [] modulepaths in
  let mainModulePath = match List.rev modulepaths with [] -> raise (LinkError "DLL must contain at least one module.") | m::_ -> m in
  let mainModuleName = Filename.chop_extension (Filename.basename mainModulePath) in
  let consume msg x xs =
    let rec iter xs' xs =
      match xs with
        [] -> raise (LinkError (msg x))
      | x'::xs -> if x = x' then xs' @ xs else iter (x'::xs') xs
    in
    iter [] xs
  in
  let impls =
    if not isLibrary then
      if not (List.mem "main : prelude.h#main()" impls) then
        if not (List.mem (Printf.sprintf "main : prelude.h#main_full(%s)" mainModuleName) impls) then
          raise (LinkError ("Program does not implement a function 'main' that implements function type 'main' or 'main_full' declared in prelude.h. Use the '-shared' option to suppress this error."))
        else
          consume (fun _ -> "Could not consume the main module") ("module " ^ mainModuleName) impls
      else
        impls
    else
      impls
  in
  let impls =
    let rec iter impls exports =
      match exports with
        [] -> impls
      | exportPath::exports ->
        let lines = read_file_lines exportPath ("Could not find export manifest file '" ^ exportPath ^ "'") in
        let rec iter' impls lines =
          match lines with
            [] -> impls
          | line::lines ->
            let (command, symbol) = parse_line line in
            match command with
              ".provides" ->
              if List.mem symbol impls then
                iter' impls lines
              else
                raise (LinkError (Printf.sprintf "Unsatisfied requirement '%s' in export manifest '%s'" symbol exportPath))
            | ".produces" ->
              let impls = consume (fun s -> Printf.sprintf "Unsatisfied requirement '%s' in export manifest '%s'" s exportPath) symbol impls in
              iter' impls lines
        in
        let impls = iter' impls lines in
        iter impls exports
    in
    iter impls exports
  in
  if emitDllManifest then
  begin
    let manifestPath = Filename.chop_extension mainModulePath ^ ".dll.vfmanifest" in
    begin
      try
        let file = open_out manifestPath in
        do_finally begin fun () ->
          List.iter (fun line -> Printf.fprintf file ".provides %s\n" line) impls
        end (fun () -> close_out file)
      with
        Sys_error s -> raise (LinkError (Printf.sprintf "Could not create DLL manifest file '%s': %s" manifestPath s))
    end;
    Printf.fprintf stderr "Written %s\n" manifestPath
  end