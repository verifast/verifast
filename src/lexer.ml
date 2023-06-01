open Big_int
open Num
open Util
open Ast
open Stats

(* Region: lexical analysis *)

(*

Processing of comments and annotation regions: compliance with C
================================================================

- In the C standard (C11), multiline comments (/**/) do not nest.
- VeriFast treats VeriFast multiline comments (/*[^@] ... [^@]*/) correctly, since it does the same thing as C.
- The VeriFast preprocessor should not allow /*@ and @*/ tokens inside preprocessor directives. This ensures that preprocessing preserves annotation ranges.
- Theorem: In any .c file that is accepted by both VeriFast and C, each VeriFast multiline annotation coincides exactly with a C multiline comment.
  Proof:
  - If there are no occurrences of /* or */ inside the annotation, this is trivially true.
  - If there is a /* inside the annotation, VF requires a */ before the end of the annotation. As a result, the @*/ that terminates the annotation will be
    outside a comment as far as C is concerned, and therefore will be seen as illegal by C. This contradicts the assumption that the file is accepted by C.
  - If there is no /* but a */ inside the annotation:
    - If the */ is not inside a string literal, this is considered illegal by VeriFast.
    - If the */ is inside a string literal, we end up in the same case as where there is a /* inside the annotation. The @*/ will be considered illegal by C.
  [TODO: Make this proof more rigorous.]
- Theorem: single-line annotations (//@) coincide with C single-line comments.
  Proof: This follows from the fact that VF and C agree on newlines.

*)

let latin1_to_utf8 text =
  let n = String.length text in
  let rec iter i =
    if i = n then
      text
    else if text.[i] <= '\x7f' then
      iter (i + 1)
    else begin
      let b = Buffer.create (2 * n) in
      Buffer.add_substring b text 0 i;
      for i = i to n - 1 do
        let c = text.[i] in
        if c <= '\x7f' then
          Buffer.add_char b c
        else begin
          Buffer.add_char b (char_of_int ((int_of_char c lsr 6) lor 0xC0));
          Buffer.add_char b (char_of_int ((int_of_char c land 0x3f) lor 0x80))
        end
      done;
      Buffer.contents b
    end
  in
  iter 0

let utf8_byte_order_mark = "\xEF\xBB\xBF"

let file_to_utf8 s =
  if startswith s utf8_byte_order_mark then
    String.sub s 3 (String.length s - 3)
  else
    latin1_to_utf8 s

let utf8_to_file s =
  (* First, find the largest substring that's ASCII *)
  let n = String.length s in
  let rec ascii i =
    if i = n then
      s
    else if s.[i] <= '\x7f' then
      ascii (i + 1)
    else begin
      (* We found a non-ASCII character. *)
      (* Check if it's all Latin 1. *)
      let rec is_latin1 i =
        if i = n then
          true
        else if s.[i] <= '\xC3' then
          is_latin1 (i + 1)
        else
          false
      in
      if is_latin1 i then begin
        let b = Buffer.create n in
        Buffer.add_substring b s 0 i;
        let rec add_latin1_chars i =
          if i = n then
            ()
          else if s.[i] <= '\x7f' then begin
            Buffer.add_char b s.[i];
            add_latin1_chars (i + 1)
          end else begin
            Buffer.add_char b (char_of_int (((int_of_char s.[i] land 0x03) lsl 6) lor (int_of_char s.[i + 1] land 0x3f)));
            add_latin1_chars (i + 2)
          end
        in
        add_latin1_chars i;
        Buffer.contents b
      end else
        utf8_byte_order_mark ^ s
    end
  in
  ascii 0

let get_first_line_tokens text =
  let n = String.length text in
  let rec first_line_tokens i =
    if i = n then
      []
    else
      match text.[i] with
        'A'..'Z'|'a'..'z'|'0'..'9'|'_' -> ident_token i (i + 1)
      | ' '|'\t' -> first_line_tokens (i + 1)
      | '\r'|'\n' -> []
      | '{' -> brace_block (i + 1) (i + 1)
      | c -> Printf.sprintf "%c" c::first_line_tokens (i + 1)
  and ident_token start i =
    match if i = n then None else Some text.[i] with
      Some ('A'..'Z'|'a'..'z'|'0'..'9'|'_'|'.') -> ident_token start (i + 1)
    | _ -> String.sub text start (i - start)::first_line_tokens i
  and brace_block start i =
    match if i = n then None else Some text.[i] with
      None|Some ('}'|'\r'|'\n') -> String.sub text start (i - start)::first_line_tokens i
    | _ -> brace_block start (i + 1)
  in
  first_line_tokens 0

let split_into_words text =
  let n = String.length text in
  let buf = Buffer.create 10 in
  let rec words i =
    if i = n then
      []
    else
      match text.[i] with
        ' ' -> words (i + 1)
      | _ -> Buffer.clear buf; word i
  and word i =
    if i = n then
      [Buffer.contents buf]
    else
      match text.[i] with
        ' ' -> let word = Buffer.contents buf in word::words (i + 1)
      | '"' -> quoted_word (i + 1)
      | c -> Buffer.add_char buf c; word (i + 1)
  and quoted_word i =
    if i = n then
      [Buffer.contents buf]
    else
      match text.[i] with
        '"' -> word (i + 1)
      | c -> Buffer.add_char buf c; quoted_word (i + 1)
  in
  words 0

type file_options = {
  annot_char: char;
  tab_size: int;
  prover: string option;
  bindings: (string * string option) list
}

exception FileOptionsError of string

let default_file_options =
  {annot_char='@'; tab_size=8; prover=None; bindings=[]}

let get_file_options text =
  let tokens = get_first_line_tokens text in
  let rec iter opts toks =
    match toks with
      "verifast_annotation_char"::":"::c::toks when String.length c = 1 -> iter {opts with annot_char=c.[0]} toks
    | "tab_size"::":"::n::toks ->
      let tabSize =
        match int_of_string n with
          exception Failure _ -> opts.tab_size
        | n -> n
      in
      iter {opts with tab_size=tabSize} toks
    | "verifast_options"::body::toks ->
      let body_words = split_into_words body in
      let rec process_words opts words =
        match words with
          [] -> iter opts toks
        | word::words ->
          match String.index_opt word ':' with
            None ->
            process_words {opts with bindings=(word, None)::opts.bindings} words
          | Some k ->
            let paramName = String.sub word 0 k in
            let arg = String.sub word (k + 1) (String.length word - k - 1) in
            match paramName with
              "prover" -> process_words {opts with prover=Some arg} words
            | _ -> process_words {opts with bindings=(paramName, Some arg)::opts.bindings} words
      in
      process_words opts body_words 
    | tok::toks ->
      iter opts toks
    | [] -> opts
  in
  iter default_file_options tokens

let readFileOptions path =
  let chan = open_in path in
  let line = try input_line chan with End_of_file -> "" in
  close_in chan;
  get_file_options line

let readFile path =
  let chan, close_chan =
    if path = "<stdin>.c" || path = "<stdin>.java" then
      (stdin, fun _ -> ())  (* read file from standard input; used for the web interface *)
    else
      (open_in_bin path, close_in)
  in
  let s = input_fully chan in
  close_chan chan;
  file_to_utf8 s

type include_kind =
  DoubleQuoteInclude
| AngleBracketInclude

type token = (* ?token *)
  | Kwd of string
  | Ident of string
  | Int of big_int * bool (* true = decimal, false = hex or octal *) * bool (* true = suffix u or U *) * int_literal_lsuffix * string
  | RealToken of big_int  (* Tokens of the form 123r. Used to distinguish 1r/2, denoting one half, from 1/2, which evaluates to zero, in a context that does not require an expression of type 'real'. *)
  | RationalToken of num * float_literal_suffix option      (* Rational number literals. E.g. 0.5, 3.14, 3e8, 6.62607004E-34. Used for floating-point literals in real code, and for real number literals in annotations. Using the arbitrary-precision 'num' type instead of the OCaml 'float' type to avoid rounding errors. *)
  | String of string
  | AngleBracketString of string
  | CharToken of char
  | BeginInclude of
      include_kind
      (** string of file included as written in the sourcecode, e.g. "../test.h" *)
      * string
      (** resolved filename of included file, e.g. "/home/jack/verifast-0.0/bin/stdio.h" *)
      * string
  | SecondaryInclude of
      (** Same as first string of BeginInclude *)
      string
      (** Same as second string of BeginInclude *)
      * string
  | EndInclude
  | Eol
  | ErrorToken
  | Eof
  | PrimePrefixedIdent of string (* Rust lifetime token, e.g. 'abc *)

let string_of_include_kind = function
  DoubleQuoteInclude -> "DoubleQuoteInclude"
| AngleBracketInclude -> "AngleBracketInclude"

let string_of_token t =
  begin match t with
    Kwd(s) -> "Keyword:" ^ s
  | Ident(s) -> "Identifier:" ^ s
  | Int(bi, dec, usuffix, lsuffix, text) ->
    "Int:" ^ Big_int.string_of_big_int bi ^
      (if usuffix then "U" else "") ^
      (match lsuffix with NoLSuffix -> "" | LSuffix -> "L" | LLSuffix -> "LL") ^
      (if dec then "(decimal)" else "(originally hex or octal)") ^
      ("'" ^ text ^ "'")
  | RealToken(bi) -> "RealToken:" ^ (Big_int.string_of_big_int bi)
  | RationalToken(n, suffix) -> "RationalToken:" ^ (Num.string_of_num n) ^ (match suffix with None -> "" | Some FloatFSuffix -> "f" | Some FloatLSuffix -> "l")
  | String(s) -> "String: " ^ s
  | AngleBracketString(s) -> "AngleBracketString: " ^ s
  | CharToken(ch) -> "Char: " ^ (Char.escaped ch)
  | BeginInclude(kind, s, _) -> "BeginInclude(" ^ string_of_include_kind kind ^ "): " ^ s
  | SecondaryInclude(s, _) -> "SecondaryInclude: " ^ s
  | EndInclude -> "EndInclude"
  | Eol -> "Eol"
  | Eof -> "Eof"
  | ErrorToken -> "Error"
  end

(* necessary because e.g. for two Big_ints bi1 bi2, the comparison bi1 = bi2 is not allowed *)
let compare_tokens t1 t2 =
  begin match (t1,t2) with
    (None,None) -> true
  | (Some(_,Int(bi1,dec1,u1,l1,text1)),Some(_,Int(bi2,dec2,u2,l2,text2))) -> text1 = text2
  | (Some(_,RealToken(bi1)),Some(_,RealToken(bi2))) -> compare_big_int bi1 bi2 = 0
  | (Some(_,RationalToken(n1,suffix1)),Some(_,RationalToken(n2,suffix2))) -> Num.eq_num n1 n2 && suffix1 = suffix2
  | (Some(_,t1),Some(_,t2)) -> t1 = t2
  | _ -> false
end

let rec print_tokens tokens =
  match tokens with
    [(_, tok)] -> Printf.printf "%s\n" (string_of_token tok)
  | (_, tok) :: xs -> Printf.printf "%s, " (string_of_token tok); print_tokens xs
  | [] -> Printf.printf "\n"

exception ParseException of loc * string
let error l msg = raise (ParseException(l, msg))
exception PreprocessorDivergence of loc0 * string

(** Like the Stream module of the O'Caml library, except that it supports a limited form of backtracking using [push].
    Used implicitly by the parser. *)
module Stream = struct
  exception Failure
  exception Error of string
  type 'a t = (int -> 'a option) * (int ref) * ('a option list ref)
  let from f = (f, ref 0, ref [])
  let of_list xs =
    let xs = ref xs in
    from begin fun _ ->
      match !xs with
        [] -> None
      | x::xs0 -> xs := xs0; Some x
    end
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
        else if int_of_char 'a' <= c && c <= int_of_char 'f' then
          c - int_of_char 'a' + 10
        else
          c - int_of_char 'A' + 10
      in
      iter (k - 1) (mult_int_big_int 16 weight) (add_big_int sum (mult_int_big_int digit weight))
  in
  iter (String.length s - 1) unit_big_int zero_big_int

let big_int_of_octal_string s =
  let rec iter k weight sum =
    if k < 0 then
      sum
    else
      let c = int_of_char (s.[k]) in
      let digit = c - (int_of_char '0') in
      iter (k - 1) (mult_int_big_int 8 weight) (add_big_int sum (mult_int_big_int digit weight))
  in
  iter (String.length s - 1) unit_big_int zero_big_int

(** For syntax highlighting. *)

type decl_kind =
  | DeclKind_HeaderFile
  | DeclKind_InductiveType
  | DeclKind_Struct
  | DeclKind_Union
  | DeclKind_FuncType
  | DeclKind_Class
  | DeclKind_Interface
  | DeclKind_AbstractType
  | DeclKind_Typedef
  | DeclKind_InductiveCtor
  | DeclKind_Predicate
  | DeclKind_RegularFunction
  | DeclKind_LemmaFunction
  | DeclKind_FixpointFunction
  | DeclKind_PureFunction
  | DeclKind_GlobalVar
  | DeclKind_Method
  | DeclKind_Macro

type range_kind = (* ?range_kind *)
    KeywordRange
  | GhostKeywordRange
  | GhostRange
  | GhostRangeDelimiter
  | CommentRange
  | ErrorRange

let string_of_range_kind = function
  | KeywordRange        -> "KeywordRange"
  | GhostKeywordRange   -> "GhostKeywordRange"
  | GhostRange          -> "GhostRange"
  | GhostRangeDelimiter -> "GhostRangeDelimiter"
  | CommentRange        -> "CommentRange"
  | ErrorRange          -> "ErrorRange"

(** The lexer.
    @param reportShouldFail Function that will be called whenever a should-fail directive is found in the source code.
      Should-fail directives are of the form //~ and are used for writing negative VeriFast test inputs. See tests/errors.
  *)
let make_lexer_core keywords ghostKeywords startpos text reportRange inComment inGhostRange exceptionOnError reportShouldFail annotChar =
  let textlength = String.length text in
  let textpos = ref 0 in
  let line = ref 1 in
  let linepos = ref 0 in
  let path =
    match startpos with
      (p, l, c) ->
        line := l;
        linepos := -c + 1;
        p
  in
  let new_loc_line () =
      line := !line + 1;
      linepos := !textpos
  in
  
  let rec skip_backslashed_newlines () =
    let pos = !textpos in
    if pos < textlength - 1 && text.[pos] = '\\' && (text.[pos + 1] = '\n' || text.[pos + 1] = '\r') then begin
      if text.[pos + 1] = '\r' && pos < textlength - 2 && text.[pos + 2] = '\n' then
        textpos := pos + 3
      else
        textpos := pos + 2;
      new_loc_line ();
      skip_backslashed_newlines ()
    end
  in
  
  let text_peek () = if !textpos = textlength then '\000' else text.[!textpos] in
  let text_peekn n = 
    let p = !textpos + n in
    if p < textlength then text.[p]
    else '\000' 
  in

  let text_junk () = incr textpos; skip_backslashed_newlines () in
  
  let annotEnd = Printf.sprintf "%c*/" annotChar in
  
  let in_comment = ref inComment in
  let in_ghost_range = ref inGhostRange in

  let eof_emitted = ref false in
  
  let buffer = Buffer.create 32 in
  
  let reset_buffer () = Buffer.reset buffer in

  let store c = Buffer.add_char buffer c in

  let get_string () =
    let s = Buffer.contents buffer in Buffer.reset buffer; s
  in

  let peek_string () =
    Buffer.contents buffer
  in

  let tokenpos = ref 0 in
  let token_srcpos = ref (path, !line, !textpos - !linepos + 1) in

  let current_srcpos() = (path, !line, !textpos - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in
  let error msg = error (Lexed (current_loc())) msg in

  let in_single_line_annotation = ref false in
  
  let ghost_range_start: srcpos option ref = ref (if inGhostRange then Some (current_srcpos()) else None) in

  let in_include_directive = ref false in
 
  let ignore_eol = ref true in
  
  (* Statistics *)
  let non_ghost_line_count = ref 0 in
  let ghost_line_count = ref 0 in
  let mixed_line_count = ref 0 in
  let last_line_with_non_ghost = ref 0 in
  let last_line_with_ghost = ref 0 in
  
  let report_nontrivial_token () =
    if !ghost_range_start <> None then begin
      if !last_line_with_ghost < !line then begin
        last_line_with_ghost := !line;
        incr ghost_line_count;
        if !last_line_with_non_ghost = !line then incr mixed_line_count
      end
    end else begin
      if !last_line_with_non_ghost < !line then begin
        last_line_with_non_ghost := !line;
        incr non_ghost_line_count;
        if !last_line_with_ghost = !line then incr mixed_line_count
      end
    end
  in
  
  let kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  let ghost_kwd_table = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add ghost_kwd_table s (Kwd s)) (keywords @ ghostKeywords);
  let get_kwd_table() = if !ghost_range_start = None then kwd_table else ghost_kwd_table in
  let ident_or_keyword id isAlpha =
    report_nontrivial_token();
    try
      let t = Hashtbl.find (get_kwd_table()) id in
      if isAlpha then
        reportRange (if !ghost_range_start = None then KeywordRange else GhostKeywordRange) (current_loc());
      if id = "include" then in_include_directive := true; 
      t
    with
      Not_found -> Ident id
  and keyword_or_error s =
    try Hashtbl.find (get_kwd_table()) s with
      Not_found -> error ("Illegal character: " ^ s)
  in
  let start_token() =
    tokenpos := !textpos;
    token_srcpos := current_srcpos()
  in
  let rec next_token () =
    if !in_comment then
    begin
      in_comment := false;
      multiline_comment ()
    end
    else
    let new_line old_line old_column =
      new_loc_line ();
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        ghost_range_end_at (path, old_line, old_column); (* Do not include the newline in the ghost range; needed to make local syntax highlighting refresh hack work in vfide. *)
        Some (Kwd "@*/")
      ) else if !ignore_eol then
        next_token ()
      else
        Some Eol
    in
    match text_peek () with
      (' ' | '\009' | '\026' | '\012') ->
        text_junk (); next_token ()
    | ('\010'|'\013') as c ->
        start_token();
        let old_line = !line in
        let old_column = !textpos - !linepos + 1 in
        if c = '\013' && !textpos + 1 < textlength && text.[!textpos + 1] = '\010' then incr textpos;
        text_junk ();
        new_line old_line old_column
    | ('A'..'Z' | 'a'..'z' | '_' | '\128'..'\255') as c ->
        start_token();
        text_junk ();
        reset_buffer (); store c;
        ident ()
    | '(' -> start_token(); text_junk (); Some(ident_or_keyword "(" false)
    | ('<' as c) ->
        start_token();
        text_junk ();
        if !in_include_directive then
         ( reset_buffer (); Some (AngleBracketString (string ())) )
         else
         ( reset_buffer (); store c; ident2 () )
    | '!' ->
      start_token(); text_junk ();
      if text_peek() = '=' then begin
        text_junk ();
        Some (ident_or_keyword "!=" false)
      end else
        Some (ident_or_keyword "!" false)
    | ('%' | '&' | '$' | '#' | '+' | '-' | '=' | '>' |
       '?' | '@' | '\\' | '~' | '^' | '|' as c) ->
        start_token();
        text_junk ();
        reset_buffer (); store c; ident2 ()
    | '.' ->
      start_token(); text_junk();
      if text_peek() = '.' then begin
        text_junk();
        if text_peek() = '.' then begin
          text_junk();
          Some (keyword_or_error "...")
        end else
          Some (keyword_or_error "..")
      end else
        Some (keyword_or_error ".")
    | ':' -> 
      start_token();
      text_junk ();
      Some (keyword_or_error ":")
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
        begin match text_peek (), c with
          '\'', _ -> text_junk (); Some (CharToken c)
        | _, ('A'..'Z'|'a'..'z'|'_') when Hashtbl.mem kwd_table "'a" ->
          reset_buffer ();
          store c;
          let rec iter () =
            match text_peek () with
              'A'..'Z'|'a'..'z'|'0'..'9'|'_' as c ->
              text_junk ();
              store c;
              iter ()
            | _ ->
              Some (PrimePrefixedIdent (get_string ()))
          in
          iter ()
        | _ -> error "Single quote expected."
        end
    | '"' ->
        if !in_include_directive then in_include_directive := false;
        start_token();
        text_junk ();
        reset_buffer (); Some (String (string ()))
    | '/' -> start_token(); text_junk (); maybe_comment ()
    | '\000' ->
      if !eof_emitted then None else begin
      start_token();
      in_ghost_range := !ghost_range_start <> None;
      ghost_range_end();
      !stats#overhead ~path:path ~nonGhostLineCount:!non_ghost_line_count ~ghostLineCount:!ghost_line_count ~mixedLineCount:!mixed_line_count;
      eof_emitted := true;
      Some Eof
      end
    | '*' -> start_token(); text_junk(); begin match text_peek() with '=' -> text_junk(); Some (keyword_or_error "*=") | _ -> Some (keyword_or_error "*") end
    | c -> start_token(); text_junk (); Some (keyword_or_error (String.make 1 c))
  and ident () =
    match text_peek () with
      ('A'..'Z' | 'a'..'z' | '\128'..'\255' | '0'..'9' | '_' | '\'' | '$') as c ->
      text_junk (); store c; ident ()
    (* for C++ nested names, e.g. foo::bar *)
    | ':' when (text_peekn 1) = ':' ->
      text_junk (); text_junk (); store ':'; store ':'; ident ()
    | _ -> Some (ident_or_keyword (get_string ()) true)
  and ident2 () =
    match text_peek () with
      ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' |
       '>' | '?' | '@' | '\\' | '~' | '^' | '|' | '*' as c) ->
        text_junk (); store c; ident2 ()
    | _ ->
      let s = get_string() in
      if s = annotEnd then
      begin
        ghost_range_end();
        reportRange GhostRangeDelimiter (current_loc());
        Some (Kwd "@*/")
      end
      else
        Some (ident_or_keyword s false)
  and number () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; number ()
    | 'x' -> text_junk (); store 'x'; hex_number ()
    | '.' when !textpos + 1 < textlength && (match text.[!textpos + 1] with '0'..'9' -> true | _ -> false) ->
        text_junk (); store '.'; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | ('r') ->
        text_junk (); Some (RealToken (big_int_of_string (get_string ())))
    | _ ->
        begin
          let str = peek_string () in
          if (str.[0] = '0') then
            int_suffix (big_int_of_octal_string str) false
          else
            int_suffix (big_int_of_string str) true
        end
  and int_suffix value is_decimal =
    let cont usuffix lsuffix = Some (Int (value, is_decimal, usuffix, lsuffix, get_string ())) in
    match text_peek () with
      'u'|'U' as c ->
      text_junk ();
      store c;
      begin match text_peek () with
        'l'|'L' as c ->
        text_junk ();
        store c;
        begin match text_peek () with
          'l'|'L'  as c ->
          text_junk ();
          store c;
          cont true LLSuffix
        | _ ->
          cont true LSuffix
        end
      | _ ->
        cont true NoLSuffix
      end
    | 'l'|'L' as c ->
      text_junk ();
      store c;
      begin match text_peek () with
        'l'|'L' as c ->
        text_junk ();
        store c;
        begin match text_peek () with
          'u'|'U' as c ->
          text_junk ();
          store c;
          cont true LLSuffix
        | _ ->
          cont false LLSuffix
        end
      | 'u'|'U' as c ->
        text_junk ();
        store c;
        cont true LSuffix
      | _ ->
        cont false LSuffix
      end
    | _ ->
      cont false NoLSuffix
  and hex_number () =
    match text_peek () with
      ('0'..'9' | 'A'..'F' | 'a'..'f') as c -> text_junk (); store c; hex_number ()
    | '.' -> text_junk (); store '.'; hex_fraction ()
    | ('p'|'P') as c -> text_junk (); store c; hex_fraction_exponent ()
    | '_' -> text_junk (); hex_number ()  (* Not valid in C but useful in annotations *)
    | _ -> int_suffix (big_int_of_hex_string (peek_string ())) false
  and hex_fraction () =
    match text_peek () with
      ('0'..'9' | 'A'..'F' | 'a'..'f') as c -> text_junk (); store c; hex_fraction ()
    | '_' -> text_junk (); hex_fraction ()  (* Not valid in C but useful in annotations *)
    | ('p'|'P') as c -> text_junk (); store c; hex_fraction_exponent ()
    | _ -> fraction_suffix (num_of_hex_fraction (get_string ()))
  and hex_fraction_exponent () =
    match text_peek () with
      '-' -> text_junk (); store '-'; hex_fraction_exponent_digits ()
    | _ -> hex_fraction_exponent_digits ()
  and hex_fraction_exponent_digits () =
    match text_peek () with
      '0'..'9' as c -> text_junk (); store c; hex_fraction_exponent_digits ()
    | _ -> fraction_suffix (num_of_hex_fraction (get_string ()))
  and fraction_suffix v =
    match text_peek () with
      'f'|'F' -> text_junk (); Some (RationalToken (v, Some FloatFSuffix))
    | 'l'|'L' -> text_junk (); Some (RationalToken (v, Some FloatLSuffix))
    | _ -> Some (RationalToken (v, None))
  and decimal_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | _ -> fraction_suffix (num_of_decimal_fraction (get_string ()))
  and exponent_part () =
    match text_peek () with
      ('+' | '-' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> end_exponent_part ()
  and end_exponent_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> fraction_suffix (num_of_decimal_fraction (get_string ()))
  and string () =
    match text_peek () with
      '"' -> text_junk (); get_string ()
    | '>' as c -> 
        text_junk ();
        if !in_include_directive then
         begin
          in_include_directive := false;
          get_string ()
         end
         else
         begin
          store c; string ()
         end;
    | '\\' ->
        text_junk ();
        let c =
          try escape () with
            Stream.Failure -> error "Bad string literal."
        in
        store c; string ()
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); store c; string ()
  and char () =
    match text_peek () with
      '\\' ->
        text_junk ();
        begin try escape () with
          Stream.Failure -> error "Bad character literal."
        end
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); c
  and escape () =
    match text_peek () with
      'n' -> text_junk (); '\n'
    | 'r' -> text_junk (); '\r'
    | 't' -> text_junk (); '\t'
    | ('0'..'3' as c1) ->   (* octal *)
        text_junk ();
        begin match text_peek () with
          ('0'..'7' as c2) ->
            text_junk ();
            begin match text_peek () with
              ('0'..'7' as c3) ->
                text_junk ();
                Char.chr
                  ((Char.code c1 - 48) * 64 + (Char.code c2 - 48) * 8 +
                     (Char.code c3 - 48))
            | _ -> Char.chr ((Char.code c1 - 48) * 64 + (Char.code c2 - 48))
            end
        | _ -> Char.chr (Char.code c1 - 48)
        end
    | 'x' ->   (* hex *)
      text_junk ();
      let hex_digit () =
        match text_peek() with
          '0'..'9' as c -> text_junk (); Char.code c - Char.code '0'
        | 'A'..'F' as c -> text_junk (); Char.code c - Char.code 'A' + 10
        | 'a'..'f' as c -> text_junk (); Char.code c - Char.code 'a' + 10
        | _ -> raise Stream.Failure
      in
      let d1 = hex_digit () in
      let d2 = hex_digit () in
      Char.chr (d1 * 16 + d2)
    | c when c < ' ' -> raise Stream.Failure
    | c -> text_junk (); c
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
          c when c = annotChar ->
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
            ghost_range_end_at !token_srcpos;
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
          c when c = annotChar ->
          text_junk ();
          if !ghost_range_start <> None then raise Stream.Failure;
          ghost_range_start := Some !token_srcpos;
          reportRange GhostRangeDelimiter (current_loc());
          Some (Kwd "/*@")
        | '~' -> text_junk (); directive (); multiline_comment ()
        | _ -> multiline_comment ()
      )
    | '=' ->
      text_junk();
      Some (keyword_or_error "/=")
    | _ -> Some (keyword_or_error "/")
  and directive () =
    let directive = Buffer.create 20 in
    let loc = current_loc () in
    let rec iter () =
      match text_peek () with
        'a'..'z'|'_' as c ->
        text_junk ();
        Buffer.add_char directive c;
        iter ()
      | _ ->
        reportShouldFail (Buffer.contents directive) loc
    in
    iter ()
  and single_line_comment () =
    match text_peek () with
      '~' -> text_junk (); directive (); single_line_comment_rest ()
    | _ -> single_line_comment_rest ()
  and single_line_comment_rest () =
    match text_peek () with
      '\010' | '\013' | '\000' -> reportRange CommentRange (current_loc())
    | c -> text_junk (); single_line_comment_rest ()
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

let make_lexer_helper keywords ghostKeywords path text reportRange inComment inGhostRange exceptionOnError reportShouldFail annotChar =
  let startpos = (path, 1, 1) in
  make_lexer_core keywords ghostKeywords startpos text reportRange inComment inGhostRange exceptionOnError reportShouldFail annotChar

let make_lexer keywords ghostKeywords path text reportRange ?inGhostRange reportShouldFail =
  let {annot_char=annotChar} = try get_file_options text with FileOptionsError msg -> raise (ParseException (Lexed ((path, 1, 1), (path, 1, 1)), msg)) in
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_helper keywords ghostKeywords path text reportRange false (match inGhostRange with None -> false | Some b -> b) true reportShouldFail annotChar in
  (loc, ignore_eol, token_stream)

(* The preprocessor *)

class type t_lexer =
  object
    method peek          : unit -> (loc0 * token) option
    method junk          : unit -> unit
    method loc           : unit -> loc0
    method reset         : unit -> unit
    method commit        : unit -> unit
    method reset_fully   : unit
  end

class tentative_lexer (lloc:unit -> loc0) (lstream:(loc0 * token) Stream.t) : t_lexer =
  object (this)
    val mutable base = 0
    val mutable fetched = 0
    val mutable counter = 0
    val mutable counter_old = 0

    val mutable buffer = Array.make 1024 None;
    val mutable locs = Array.make (1024 + 1) (lloc());

    method peek() =
      if (base + counter) < fetched then
        Array.get buffer (base + counter)
      else begin
        this#fetch();
        this#peek()
      end
    method junk() =
      counter <- counter + 1;
    method loc() =
      Array.get locs (base + counter)
    method reset() =
      counter_old <- counter;
      counter <- 0;
    method commit() =
      if counter < counter_old then
        let Some (l, _) = Array.get buffer (base + counter) in
        raise (PreprocessorDivergence (l, Printf.sprintf "This token and the %d after it were consumed by the normal preprocessor but not by the context-free preprocessor" (counter_old - counter - 1)))
      else if counter_old < counter then begin
        let Some (l, _) = Array.get buffer (base + counter_old) in
        raise (PreprocessorDivergence (l, Printf.sprintf "This token and the %d after it were consumed by the context-free preprocessor but not by the normal preprocessor" (counter - counter_old - 1)))
      end;
      base <- base + counter;
      counter <- 0;
      counter_old <- 0;
    
    method private fetch () =
      if fetched < (Array.length buffer) then begin
        Array.set buffer fetched (Stream.peek (lstream));
        Stream.junk lstream;
        Array.set locs (fetched + 1) (lloc());
        fetched <- fetched + 1;
      end else begin
        let length = 2 * (Array.length buffer) in
        let b = Array.make length None in
        let l = Array.make (length + 1) dummy_loc0 in
        Array.blit buffer 0 b 0 (Array.length buffer);
        Array.blit locs 0 l 0 (Array.length locs);
        buffer <- b;
        locs <- l;
        this#fetch();
      end

    method reset_fully =
      base <- 0;
      counter <- 0;
      counter_old <- 0

  end

let construct_not_supported () = raise (Stream.Error "This construct is not supported in preprocessor conditions")
(* Mini parser which is a subset of Parser.parse_decls_core *)
let parse_operators dataModel =
let rec
  parse_operators stream = parse_disj_expr stream
and
  parse_operators_rest stream = parse_disj_expr_rest stream
and
  parse_disj_expr = function%parser
  [ parse_conj_expr as e0; [%l e = parse_disj_expr_rest e0] ] -> e
and
  parse_conj_expr = function%parser
  [ parse_bitor_expr as e0; [%l e = parse_conj_expr_rest e0] ] -> e
and
  parse_bitor_expr = function%parser
  [ parse_bitxor_expr as e0; [%l e = parse_bitor_expr_rest e0] ] -> e
and
  parse_bitxor_expr = function%parser
  [ parse_bitand_expr as e0; [%l e = parse_bitxor_expr_rest e0] ] -> e
and
  parse_bitand_expr = function%parser
  [ parse_expr_rel as e0; [%l e = parse_bitand_expr_rest e0] ] -> e
and
  parse_expr_rel = function%parser
  [ parse_truncating_expr as e0; [%l e = parse_expr_rel_rest e0] ] -> e
and
  parse_truncating_expr = function%parser
  [ parse_shift as e ] -> e
and
  parse_shift = function%parser
  [ parse_expr_arith as e0; [%l e = parse_shift_rest e0] ] -> e
and
  parse_expr_arith = function%parser
  [ parse_expr_mul as e0; [%l e = parse_expr_arith_rest e0] ] -> e
and
  parse_expr_mul = function%parser
  [ parse_expr_suffix as e0; [%l e = parse_expr_mul_rest e0] ] -> e
and
  parse_expr_suffix = function%parser
  [ parse_expr_primary as e ] -> e
and
  parse_expr_primary = function%parser
  [ (l, Ident _) ] -> IntLit (l, zero_big_int, false, false, NoLSuffix)
| [ (l, Int (n, dec, usuffix, lsuffix, _)) ] -> IntLit (l, n, dec, usuffix, lsuffix)
| [ (l, Kwd "-"); (l, Int (n, dec, usuffix, lsuffix, _)) ] -> IntLit (l, minus_big_int n, dec, usuffix, lsuffix)
| [ (l, Kwd "("); parse_operators as e0; (_, Kwd ")"); [%l e = parse_operators_rest e0] ] -> e
| [ (l, Kwd "!"); parse_expr_suffix as e ] -> Operation(l, Not, [e])
| [ (l, Kwd "INT_MIN") ] -> (match dataModel with Some {int_width} -> IntLit (l, min_signed_big_int int_width, true, false, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "INT_MAX") ] -> (match dataModel with Some {int_width} -> IntLit (l, max_signed_big_int int_width, true, false, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "UINTPTR_MAX") ] -> (match dataModel with Some {ptr_width} -> IntLit (l, max_unsigned_big_int ptr_width, true, true, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "CHAR_MIN") ] -> IntLit (l, big_int_of_string "-128", true, false, NoLSuffix)
| [ (l, Kwd "CHAR_MAX") ] -> IntLit (l, big_int_of_string "127", true, false, NoLSuffix)
| [ (l, Kwd "UCHAR_MAX") ] -> IntLit (l, big_int_of_string "255", true, false, NoLSuffix)
| [ (l, Kwd "SHRT_MIN") ] -> IntLit (l, big_int_of_string "-32768", true, false, NoLSuffix)
| [ (l, Kwd "SHRT_MAX") ] -> IntLit (l, big_int_of_string "32767", true, false, NoLSuffix)
| [ (l, Kwd "USHRT_MAX") ] -> IntLit (l, big_int_of_string "65535", true, false, NoLSuffix)
| [ (l, Kwd "UINT_MAX") ] -> (match dataModel with Some {int_width} -> IntLit (l, max_unsigned_big_int int_width, true, true, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "LLONG_MIN") ] -> IntLit (l, big_int_of_string "-9223372036854775808", true, false, NoLSuffix)
| [ (l, Kwd "LLONG_MAX") ] -> IntLit (l, big_int_of_string "9223372036854775807", true, false, NoLSuffix)
| [ (l, Kwd "ULLONG_MAX") ] -> IntLit (l, big_int_of_string "18446744073709551615", true, true, NoLSuffix)
| [ (l, Kwd "LONG_MIN") ] -> (match dataModel with Some {long_width} -> IntLit (l, min_signed_big_int long_width, true, false, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "LONG_MAX") ] -> (match dataModel with Some {long_width} -> IntLit (l, max_signed_big_int long_width, true, false, NoLSuffix) | _ -> construct_not_supported ())
| [ (l, Kwd "ULONG_MAX") ] -> (match dataModel with Some {long_width} -> IntLit (l, max_unsigned_big_int long_width, true, true, NoLSuffix) | _ -> construct_not_supported ())
and
  parse_expr_mul_rest e0 = function%parser
  [ (l, Kwd "*"); parse_expr_suffix as e1; [%l e = parse_expr_mul_rest (Operation (l, Mul, [e0; e1]))] ] -> e
| [ (l, Kwd "/"); parse_expr_suffix as e1; [%l e = parse_expr_mul_rest (Operation (l, Div, [e0; e1]))] ] -> e
| [ (l, Kwd "%"); parse_expr_suffix as e1; [%l e = parse_expr_mul_rest (Operation (l, Mod, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_expr_arith_rest e0 = function%parser
  [ (l, Kwd "+"); parse_expr_mul as e1; [%l e = parse_expr_arith_rest (Operation (l, Add, [e0; e1]))] ] -> e
| [ (l, Kwd "-"); parse_expr_mul as e1; [%l e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_shift_rest e0 = function%parser
  [ (l, Kwd "<<"); parse_expr_arith as e1; [%l e = parse_shift_rest (Operation (l, ShiftLeft, [e0; e1]))] ] -> e
| [ (l, Kwd ">>"); parse_expr_arith as e1; [%l e = parse_shift_rest (Operation (l, ShiftRight, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_expr_rel_rest e0 = function%parser
  [ (l, Kwd "=="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1]))] ] -> e
| [ (l, Kwd "!="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1]))] ] -> e
| [ (l, Kwd "<"); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Lt, [e0; e1]))] ] -> e
| [ (l, Kwd "<="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Le, [e0; e1]))] ] -> e
| [ (l, Kwd ">"); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Gt, [e0; e1]))] ] -> e
| [ (l, Kwd ">="); parse_truncating_expr as e1; [%l e = parse_expr_rel_rest (Operation (l, Ge, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_bitand_expr_rest e0 = function%parser
  [ (l, Kwd "&"); parse_expr_rel as e1; [%l e = parse_bitand_expr_rest (Operation (l, BitAnd, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_bitxor_expr_rest e0 = function%parser
  [ (l, Kwd "^"); parse_bitand_expr as e1; [%l e = parse_bitxor_expr_rest (Operation (l, BitXor, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_bitor_expr_rest e0 = function%parser
  [ (l, Kwd "|"); parse_bitxor_expr as e1; [%l e = parse_bitor_expr_rest (Operation (l, BitOr, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_conj_expr_rest e0 = function%parser
  [ (l, Kwd "&&"); parse_bitor_expr as e1; [%l e = parse_conj_expr_rest (Operation (l, And, [e0; e1]))] ] -> e
| [ ] -> e0
and
  parse_disj_expr_rest e0 = function%parser
  [ (l, Kwd "||"); parse_conj_expr as e1; [%l e = parse_disj_expr_rest (Operation (l, Or, [e0; e1]))] ] -> e
| [ ] -> e0
in
parse_operators

let intmax_bitwidth = 8 * (1 lsl intmax_width)

(* Evaluator for operators *)
let rec eval_operators e =
  let u, n =
    match e with
      IntLit (_, n, dec, usuffix, lsuffix) -> usuffix, n (* TODO: use dec/usuffix/lsuffix *)
    | Operation (_, (Mul|Div|Mod|Add|Sub as op), [e0; e1]) ->
      let u, n1, n2 = eval_and_convert_operands e0 e1 in
      let n =
        match op with
          Mul -> mult_big_int n1 n2
        | Div -> if sign_big_int n1 < 0 then minus_big_int (div_big_int (minus_big_int n1) n2) else div_big_int n1 n2
        | Mod -> if sign_big_int n1 < 0 then minus_big_int (mod_big_int (minus_big_int n1) n2) else mod_big_int n1 n2
        | Add -> add_big_int n1 n2
        | Sub -> sub_big_int n1 n2
      in
      u, n
    | Operation (l, (ShiftLeft|ShiftRight as op), [e0; e1]) ->
      let u1, n1 = eval_operators e0 in
      let _, n2 = eval_operators e1 in
      if sign_big_int n2 < 0 then error l "Right operand of bitwise shift operator is negative";
      if le_big_int (big_int_of_int intmax_bitwidth) n2 then error l "Right operand of bitwise shift operator is greater than or equal to the width of the left operand";
      let n =
        match op with
          ShiftLeft ->
          if sign_big_int n1 < 0 then error l "Left operand of bitwise shift left operator is negative";
          shift_left_big_int n1 (int_of_big_int n2)
        | ShiftRight ->
          (* The behavior of shift right on negative numbers is implementation-defined; however, assume sign extension since this seems to be the common behavior *)
          shift_right_big_int n1 (int_of_big_int n2)
      in
      u1, n
    | Operation (_, (Eq|Neq|Lt|Le|Gt|Ge as op), [e0; e1]) ->
      let u, n1, n2 = eval_and_convert_operands e0 e1 in
      let result =
        match op with
          Eq -> eq_big_int n1 n2
        | Neq -> not (eq_big_int n1 n2)
        | Lt -> lt_big_int n1 n2
        | Le -> le_big_int n1 n2
        | Gt -> gt_big_int n1 n2
        | Ge -> ge_big_int n1 n2
      in
      false, if result then unit_big_int else zero_big_int
    | Operation (_, (BitAnd|BitXor|BitOr as op), [e0; e1]) ->
      let u, n1, n2 = eval_and_convert_operands e0 e1 in
      let n1', n2' =
        extract_big_int n1 0 intmax_bitwidth,
        extract_big_int n2 0 intmax_bitwidth
      in
      let n =
        match op with
          BitAnd -> and_big_int n1' n2'
        | BitOr -> or_big_int n1' n2'
        | BitXor -> xor_big_int n1' n2'
      in
      let n =
        if u then n else if lt_big_int (max_signed_big_int intmax_width) n then sub_big_int n (succ_big_int (max_unsigned_big_int intmax_width)) else n
      in
      u, n
    | Operation (_, And, [e0; e1]) ->
      false, if sign_big_int (snd (eval_operators e0)) <> 0 && sign_big_int (snd (eval_operators e1)) <> 0 then unit_big_int else zero_big_int
    | Operation (_, Or, [e0; e1]) ->
      false, if sign_big_int (snd (eval_operators e0)) <> 0 || sign_big_int (snd (eval_operators e1)) <> 0 then unit_big_int else zero_big_int
    | Operation (_, Not, [e0]) ->
      false, if sign_big_int (snd (eval_operators e0)) <> 0 then zero_big_int else unit_big_int
  in
  let n =
    if u then
      extract_big_int n 0 intmax_bitwidth
    else
      if lt_big_int n (min_signed_big_int intmax_width) then
        error (expr_loc e) "Arithmetic underflow: the value of this expression is less than INTMAX_MIN"
      else if lt_big_int (max_signed_big_int intmax_width) n then
        error (expr_loc e) "Arithmetic overflow: the value of this expression is greater than INTMAX_MAX"
      else
        n
  in
  u, n
and eval_and_convert_operands e1 e2 =
  let (u1, n1), (u2, n2) = eval_operators e1, eval_operators e2 in
  (* Apply usual arithmetic conversions *)
  let u = u1 || u2 in
  let n1 = if u1 = u then n1 else extract_big_int n1 0 intmax_bitwidth in
  let n2 = if u2 = u then n2 else extract_big_int n2 0 intmax_bitwidth in
  u, n1, n2

let make_file_preprocessor0 reportMacroCall path get_macro set_macro peek junk in_ghost_range dataModel =
  let peek () =
    match peek () with
      None -> None
    | Some (l, t) -> Some (Lexed l, t)
  in
  let isGhostHeader = !in_ghost_range in
  let is_defined l x = get_macro l x <> None in
  let get_macro l x = let Some v = get_macro l x in v in
  let last_macro_used = ref (dummy_loc0, "") in
  let update_last_macro_used l x =
    if is_defined l x then begin
      match get_macro l x with
        (l, _, _) -> last_macro_used := (l, x);
    end
  in
  let defining_macro = ref false in
  let next_at_start_of_file = ref true in
  let next_at_start_of_line = ref true in
  let ghost_range_delimiter_allowed = ref false in
  let rec make_subpreprocessor callers peek junk =
    let streams = ref [] in
    let callers = ref [callers] in
    let push_list newCallers body =
      streams := Stream.of_list body::!streams;
      callers := (newCallers @ List.hd !callers)::!callers;
    in
    let pop_stream () =
      streams := List.tl !streams;
      callers := List.tl !callers;
    in
    let peek () =
      let t = 
        match !streams with 
          s::_ -> Stream.peek s
        | [] -> peek ()
      in
      if not !ghost_range_delimiter_allowed then begin match t with
        (Some (l, Kwd "/*@") | Some (l, Kwd "@*/")) -> error l "Ghost range delimiters not allowed inside preprocessor directives."
      | _ -> ()
      end;
      t
    in
    let junk () = 
      match !streams with 
        s::_ -> Stream.junk s
      | [] -> junk ()
    in
    let syntax_error l = error l "Preprocessor syntax error" in
    let rec skip_block () =
      let at_start_of_line = !next_at_start_of_line in
      next_at_start_of_line := false;
      ghost_range_delimiter_allowed := true;
      match peek () with
        Some (_, Eof) -> ghost_range_delimiter_allowed := false
      | Some (_, Eol) -> junk (); next_at_start_of_line := true; skip_block ()
      | Some (_, Kwd "#") when at_start_of_line ->
        junk ();
        begin match peek () with
          Some (_, Kwd ("endif"|"else"|"elif")) -> ghost_range_delimiter_allowed := false
        | Some (_, Kwd ("ifdef"|"ifndef"|"if")) -> junk (); skip_branches (); skip_block ()
        | Some (_, Eof) -> ghost_range_delimiter_allowed := false
        | Some _ -> junk (); skip_block ()
        end
      | _ -> junk (); skip_block ()
    and skip_branches () =
      skip_block ();
      match peek () with
        Some (l, Eof) -> syntax_error l
      | Some (_, Kwd "endif") -> junk (); ()
      | _ -> junk (); skip_branches ()
    in
    let rec skip_branch () =
      skip_block ();
      begin match peek () with
        Some (_, Kwd "endif") -> junk (); ()
      | Some (l, Kwd "elif") -> junk (); conditional l
      | Some (_, Kwd "else") -> junk (); ()
      | Some (_, Eof) -> ()
      end
    and conditional l =
      let rec condition () =
        match peek () with
          Some (_, Eof) | Some (_, Eol) -> []
        | Some (l, Ident "defined") ->
          let check lx x = 
            let cond = 
              if is_defined lx x then begin
                update_last_macro_used lx x;
                (l, Int (unit_big_int, true, false, NoLSuffix, "1"))
              end
              else (l, Int (zero_big_int, true, false, NoLSuffix, "0"))
            in
            cond::condition ()
          in
          junk ();
          begin match peek () with
            Some (lx, Ident x) ->
            junk ();
            check lx x
          | Some (_, Kwd "(") ->
            junk ();
            begin match peek () with
              Some (lx, Ident x) ->
              junk ();
              begin match peek () with
                Some (_, Kwd ")") ->
                junk ();
                check lx x
              | Some (l, _) -> syntax_error l
              end
            | Some (l, _) -> syntax_error l
            end
          | Some (l, _) -> syntax_error l
          end
        | Some t -> junk (); t::condition ()
      in
      let condition = condition () in
      let condition = macro_expand [] condition in
      let condition =
        let stream = Stream.of_list condition in
        let error msg =
          match Stream.peek stream with
            Some (l, _) -> error l msg
          | None -> error l msg
        in
        try
          parse_operators dataModel stream
        with
          Stream.Error msg -> error msg
        | Stream.Failure -> error "Parse error during preprocessing"
      in
      let _, condition = eval_operators condition in
      let isTrue = sign_big_int condition <> 0 in
      if isTrue then () else skip_branch ()
    and next_token () =
      let at_start_of_file = !next_at_start_of_file in
      next_at_start_of_file := false;
      let at_start_of_line = !next_at_start_of_line in
      next_at_start_of_line := false;
      match
        ghost_range_delimiter_allowed := true;
        let t = peek () in
        ghost_range_delimiter_allowed := false;
        t
      with
        None -> 
          if !streams = [] then
            None
          else begin
            pop_stream ();
            next_token ()
          end
      | Some t ->
      match t with
        (_, Eol) ->
           begin junk (); next_at_start_of_line := true; next_token () end
      | (l, Kwd "/*@") -> 
          if isGhostHeader then raise (ParseException (l, "Ghost range delimiters are not allowed inside ghost headers."));
          junk (); in_ghost_range := true; 
          next_at_start_of_line := at_start_of_line; Some t
      | (l, Kwd "@*/") -> 
          if isGhostHeader then raise (ParseException (l, "Ghost range delimiters are not allowed inside ghost headers."));
          junk (); in_ghost_range := false; 
          next_at_start_of_line := true; Some t
      | (l, Kwd "##") when !defining_macro -> Some t
      | (l, Kwd "#") when at_start_of_line ->
        junk ();
        begin match peek () with
        | Some (_, Eof) -> next_token ()
        | Some (l, Kwd "include") ->
          junk ();
          begin match peek () with
          | Some (l, (String s | AngleBracketString s as ss)) ->
            junk ();
            if List.mem s ["include_ignored_by_verifast.h"; "assert.h"; "limits.h"] then 
              next_token () 
            else begin
              if isGhostHeader then begin
                if not (Filename.check_suffix s ".gh") then raise (ParseException (l, "#include directive in ghost header should specify a ghost header file (whose name ends in .gh)."))
              end else begin
                if !in_ghost_range && not (Filename.check_suffix s ".gh") then raise (ParseException (l, "Ghost #include directive should specify a ghost header file (whose name ends in .gh)."));
                if not !in_ghost_range && (Filename.check_suffix s ".gh") then raise (ParseException (l, "Non-ghost #include directive should not specify a ghost header file."))
              end;
              next_at_start_of_line := true;
              let includeKind = match ss with String _ -> DoubleQuoteInclude | AngleBracketString _ -> AngleBracketInclude in
              Some (l, BeginInclude(includeKind, s, ""))
            end
          | Some (l, _) -> error l "Filename expected"
          end
        | Some (l, Kwd "define") ->
          defining_macro := true;
          junk ();
          begin match peek () with
            Some (lx, Ident x) ->
            let Lexed lx0 = lx in
            junk ();
            let has_no_whitespace_between location1 location2 =
              let Lexed (start1, stop1) = location1 in
              let (path1, line1, col1) = stop1 in
              let Lexed (start2, stop2) = location2 in
              let (path2, line2, col2) = start2 in
              col1 = col2
            in
            let params =
              match peek () with
                (* For a macro "#define FIVE (2+3)" there are no parameters
                 * even though there is a open bracket "(", so we must
                 * check whether the open bracket has preceding whitespace,
                 * hence the "when has_no_whitespace_between lx l":
                 *)
                Some (l, Kwd "(") when has_no_whitespace_between lx l->
                junk ();
                let rec params first =
                  match peek () with
                    Some (_, Kwd ")") -> junk (); []
                  | _ ->
                    if not first then begin
                      match peek () with
                        Some (_, Kwd ",") -> junk ()
                      | Some (l, _) -> error l "Expected ',' for separating macro parameters or ')' for ending macro parameter list"
                    end;
                    begin match peek () with
                      Some (_, Ident x) -> junk (); x::params false
                    | Some (_, Kwd "...") -> junk (); "..."::params false
                    | Some (l, _) -> error l "Macro parameter expected"
                    end
                in
                Some (params true)
              | _ -> None
            in
            let rec body () =
              match peek () with
                Some (_, Eof) | Some (_, Eol) -> []
              | Some t -> junk (); t::body ()
            in 
            let body = body () in
            set_macro x (Some (lx0, params, body));
            defining_macro := false;
            begin match body with
              (l, Kwd "##")::_ -> error l "## operator cannot appear at the start of a macro"
            | _ -> ()
            end;
            begin match List.rev body with
              (l, Kwd "##")::_ -> error l "## operator cannot appear at the end of a macro"
            | _ -> ()
            end;
            next_token ()
          | Some (l, _) -> error l "Macro definition syntax error"
          end
        | Some (l, Kwd "undef") ->
          junk ();
          begin match peek () with
            Some (_, Ident x) ->
            junk ();
            set_macro x None;
            next_token ()
          | Some (l, _) -> syntax_error l
          end
        | Some (l, Kwd ("ifdef"|"ifndef" as cond)) ->
          junk ();
          begin match peek () with
            Some (lx, Ident x) ->
            junk ();
            update_last_macro_used lx x;
            if is_defined lx x <> (cond = "ifdef") then
              skip_branch ();
            next_token ()
          | Some (l, _) -> syntax_error l
          end
        | Some (l, Kwd "if") ->
          junk ();
          conditional l;
          next_token ()
        | Some (l, Kwd ("elif"|"else")) ->
          junk ();
          skip_branches ();
          next_token ()
        | Some (l, Kwd "endif") -> junk (); next_token ()
        | Some (l, Kwd "pragma") ->
          junk ();
          begin match peek() with
            Some (lx, Ident "once") ->
              if not at_start_of_file then
                error lx "Pragma once is only supported at the start of a file";
              junk ();
              let Lexed lx0 = lx in
              (* Use the absolute file name as a fake macro name *)
              if is_defined lx path then
                skip_block ()
              else
                set_macro path (Some (lx0, None, []));
              next_token ()
          | Some (l, _) -> syntax_error l
          end
        | Some (l, _) -> syntax_error l
        end
      | (l, Ident x) as t when is_defined l x && not (List.mem x (List.hd !callers)) ->
        let lmacro_call = l in
        update_last_macro_used l x;
        junk ();
        let (lmacro, params, body) = get_macro l x in
        begin match lmacro_call with
          Lexed l0 -> reportMacroCall l0 lmacro
        | _ -> ()
        end;
        let concatenate tokens args =
          let concat_tokens l first second =
            let check_identifier x =
              match try_assoc x args with
                Some a ->
                begin match a with
                | [(l1, Ident id1)] -> id1
                | [(l1, Int (_, _, _, _, text))] -> text
                | _ -> error l "Unsupported use of concatenation operator in macro";
                end
              | None ->
                x
            in
            match first with
            | (l1, Ident id1) -> 
                begin
                  match second with
                  | (l2, Ident id2) -> (l2, Ident ((check_identifier id1) ^ (check_identifier id2)));
                  | (l2, Int (_, _, _, _, text)) -> (l2, Ident (check_identifier id1 ^ text))
                  | _ -> error l "Unsupported use of concatenation operator in macro";
                end
            | _ -> error l "Unsupported use of concatenation operator in macro";
          in
          let rec concat_core tokens =
            match tokens with
            | t1::(l, Kwd "##")::t2::rest -> concat_core ((concat_tokens l t1 t2)::rest)
            | t::rest -> t::(concat_core rest)
            | [] -> []
          in
          let result = concat_core tokens in
          begin match flatmap (function (l, Kwd "##") -> [l] | _ -> []) result with
            l::_ -> error l "Invalid use of concatenation operator in macro"
          | [] -> ()
          end;
          result
        in
        begin match params with
          None -> push_list [x] (concatenate body []); next_token ()
        | Some params ->
          match peek () with
            Some (_, Kwd "(") ->
            junk ();
            let args =
              let rec term parenDepth =
                match peek () with
                  Some (l, Eof) -> syntax_error l
                | Some ((_, Kwd ")") as t) -> junk (); t::if parenDepth = 1 then arg () else term (parenDepth - 1)
                | Some ((_, Kwd "(") as t) -> junk (); t::term (parenDepth + 1)
                | Some t -> junk (); t::term parenDepth
              and arg () =
                match peek () with
                  Some (_, Kwd (")"|",")) -> []
                | Some (_, Kwd "(") -> term 0
                | Some (l, Eof) -> syntax_error l
                | Some t -> junk (); t::arg ()
              in
              let binding param =
                match param with
                  "..." -> 
                  let rec varargs () =
                    match peek () with
                      Some (_, Kwd ")") -> []
                    | Some ((_, Kwd ",") as t) -> junk (); let arg0 = arg () in [t]::arg0::varargs ()
                  in
                  "__VA_ARGS__", let arg0 = arg () in List.concat (arg0::varargs ())
                | param ->
                  param, arg ()
              in
              let rec args params first =
                match params with
                  [] ->
                  begin match peek () with
                    Some (_, Kwd ")") -> junk (); []
                  | Some (l, _) -> error l "Too many macro arguments; end of argument list expected"
                  end
                | param::params ->
                  if not first then begin
                    match peek () with
                      Some (_, Kwd ",") -> junk ()
                    | Some (l, _) -> error l "Too few macro arguments; comma expected"
                  end;
                  let arg0 = binding param in
                  arg0::args params false
              in
              args params true
            in
            let body =
              concatenate body args
            in
            let args = List.map (fun (param, arg) -> (param, macro_expand [] arg)) args in
            let body =
              body |> flatmap begin function
                (lparam, Ident x) as t ->
                begin match try_assoc x args with
                  None -> [t]
                | Some value -> List.map (fun (l, t) -> (MacroParamExpansion (lparam, l), t)) value
                end
              | t -> [t]
              end
            in
            let body = List.map (fun (l, t) -> MacroExpansion (lmacro_call, l), t) body in
            push_list [x] body; next_token ()
          | _ -> Some t
        end
      | t -> junk (); Some t
    and macro_expand newCallers tokens =
      let tokensStream = Stream.of_list tokens in
      let next_token = make_subpreprocessor (newCallers @ List.hd !callers) (fun () -> Stream.peek tokensStream) (fun () -> Stream.junk tokensStream) in
      let rec get_tokens ts =
        match next_token () with
          None -> List.rev ts
        | Some t -> get_tokens (t::ts)
      in
      let ts = get_tokens [] in
      ts
    in
    next_token
  in
  (make_subpreprocessor [] peek junk, fun _ -> !last_macro_used)

let make_file_preprocessor reportMacroCall path macros ghost_macros peek junk in_ghost_range dataModel =
  let get_macros () = if !in_ghost_range then ghost_macros else macros in
  let set_macro x v =
    match v with
      Some v -> Hashtbl.replace (get_macros ()) x v
    | None -> Hashtbl.remove (get_macros ()) x
  in
  let get_macro l x =
    if !in_ghost_range then
      match Hashtbl.find_opt ghost_macros x with
        None -> Hashtbl.find_opt macros x
      | result -> result
    else
      Hashtbl.find_opt macros x
  in
  make_file_preprocessor0 reportMacroCall path get_macro set_macro peek junk in_ghost_range dataModel

type ghostness = Real | Ghost

let is_ghost_header h = Filename.check_suffix h ".gh"

let make_sound_preprocessor_core reportMacroCall make_lexer path verbose include_paths dataModel define_macros p_ghost_macros included_files =
  if verbose = -1 then Printf.printf "%10.6fs: >> start preprocessing file: %s\n" (Perf.time()) path;
  let mk_macros0 () =
    let macros0 = Hashtbl.create 10 in
    List.iter
      (fun x -> Hashtbl.replace macros0 x (dummy_loc0, None, [(dummy_loc, Int (unit_big_int, false, false, NoLSuffix, "1"))]))
      define_macros;
    macros0
  in
  let tlexers = ref [] in
  let p_macros = mk_macros0 () in
  let pps = ref [] in
  let p_last_macro_used = ref [] in
  let cfp_macros = ref [] in
  let cfp_ghost_macros = ref [] in
  let cfpps = ref [] in
  let curr_tlexer = ref (new tentative_lexer (fun () -> dummy_loc0) (Stream.of_list [])) in
  let path_is_ghost_header = is_ghost_header path in
  let p_in_ghost_range = ref path_is_ghost_header in
  let cfp_in_ghost_range = ref path_is_ghost_header in
  let paths = ref [] in  
  let mk_tlexer path =
    assert (!p_in_ghost_range = is_ghost_header path);
    let (loc, lexer_ignore_eol, stream) = make_lexer path include_paths ~inGhostRange:!p_in_ghost_range in
    lexer_ignore_eol := false;
    new tentative_lexer loc stream
  in
  let tlexer_cache = ref [] in
  let get_tlexer l path =
    match List.assoc_opt path !tlexer_cache with
      Some tlexer ->
      if List.mem path !paths then raise (ParseException (l, "Recursive inclusion of header '" ^ path ^ "' by header '" ^ String.concat "' included by '" !paths ^ "'. Recursive inclusion is not supported by VeriFast."));
      tlexer#reset_fully;
      tlexer
    | None ->
      let tlexer = mk_tlexer path in
      tlexer_cache := (path, tlexer)::!tlexer_cache;
      tlexer
  in
  let push_tlexer l path =
    curr_tlexer := get_tlexer l path;
    tlexers := !curr_tlexer::!tlexers;
    paths := path::!paths
  in
  let pop_tlexer () =
    tlexers := List.tl !tlexers;
    curr_tlexer := List.hd !tlexers;
    paths := List.tl !paths
  in
  push_tlexer dummy_loc path;
  let cfp_header_macros_cache = ref [] in
  let cfp_header_ghost_macros_cache = ref [] in
  let get_cfp_header_macros_cache gh =
    match gh with
      Real -> cfp_header_macros_cache
    | Ghost -> cfp_header_ghost_macros_cache
  in
  let cfp_end_include gh macros1 macros2 =
    let cache = get_cfp_header_macros_cache gh in
    let path = List.hd !paths in
    let macros1 =
      match List.assoc_opt path !cache with
        None ->
        cache := (path, macros1)::!cache;
        macros1
      | Some macros1 ->
        macros1
    in
    Hashtbl.iter (fun k v -> Hashtbl.replace macros2 k v) macros1
  in
  let current_loc () = !curr_tlexer#loc() in
  let () =
    let pp0, last_macro_used0 = make_file_preprocessor reportMacroCall path p_macros p_ghost_macros (fun () -> !curr_tlexer#peek ()) (fun () -> !curr_tlexer#junk ()) p_in_ghost_range dataModel in
    pps := [pp0];
    p_last_macro_used := [last_macro_used0]
  in
  let last_macro_used () =
    (List.hd !p_last_macro_used) ()
  in
  let () =
    let macros0 = mk_macros0 () in
    let ghost_macros0 = Hashtbl.create 10 in
    cfp_macros := [macros0];
    cfp_ghost_macros := [ghost_macros0];
    let cfpp0, _ = make_file_preprocessor reportMacroCall path macros0 ghost_macros0 (fun () -> !curr_tlexer#peek ()) (fun () -> !curr_tlexer#junk ()) cfp_in_ghost_range dataModel in
    cfpps := [cfpp0]
  in
  let pop_pps () =
    begin
      pps := List.tl !pps;
      p_last_macro_used := List.tl !p_last_macro_used
    end;
    begin
      let macros1::macros = !cfp_macros in
      cfp_end_include Real macros1 (List.hd macros);
      cfp_macros := macros;
      let ghost_macros1::ghost_macros = !cfp_ghost_macros in
      cfp_end_include Ghost ghost_macros1 (List.hd ghost_macros);
      cfp_ghost_macros := ghost_macros;
      cfpps := List.tl !cfpps
    end
  in
  let p_next () = (List.hd !pps) () in
  let cfp_next () = (List.hd !cfpps) () in
  let divergence l s = 
    begin match !tlexers with _::_::_ -> pop_tlexer() | _ -> () end;
    raise (PreprocessorDivergence (l , s))    
  in
  let rec next_token () =
    let p_t = p_next() in
    !curr_tlexer#reset();
    let cfp_t = cfp_next() in
    !curr_tlexer#commit();
    if compare_tokens p_t cfp_t && !p_in_ghost_range = !cfp_in_ghost_range then begin
      begin match p_t with
        Some (l,BeginInclude(kind, i, _)) ->    
          let path0 = List.hd !paths in
          let includepaths = (match kind with DoubleQuoteInclude -> [Filename.dirname path0] | AngleBracketInclude -> []) @ include_paths @ [!bindir] in
          
          (** Searches the directory in includepaths that contains the file i (can contain directory names).
           *  Returns the path of the found file.
           * 
           * What to do in case of multiple matches?
           *
           * ISO/IEC 9899:TC2 says:
           *  A preprocessing directive of the form
           *     # include "q-char-sequence" new-line
           *   causes the replacement of that directive by the entire contents of the source file identified
           *   by the specified sequence between the " delimiters. The named source file is searched
           *   for in an implementation-defined manner. If this search is not supported, or if the search
           *   fails, the directive is reprocessed as if it read
           *     # include <h-char-sequence> new-line
           *   with the identical contained sequence (including > characters, if any) from the original
           *   directive.
           * 
           * So it does not even says that 'include "..."' should search in the current directory.
           * So when writing '#include "stdio.h"', it's up to the compiler whether it includes
           * ./stdio.h or /usr/include/stdio.h.
           *
           * To keep things practical, we make the assumption that the
           * compiler searches in the directory of the includer for an
           * ""-include, and does not search in the directory of the
           * includer for an <>-include. This is the behaviour of GCC.
           * VeriFast thus has the same behaviour.
           *
           * Alternatively, we could try to avoid all this messy problems by just disallowing including files 
           * that can have multiple candidates of physical files to be included.
           * (but this breaks examples and VeriFast does not distinguish between
           * verifast-standard library (e.g. list.gh, ...) and C standard library
           * (e.g. stdio.h), they're both in bin/, which is a problem if one but not
           * the other is to be used in an example).
           *
           * " <-- this line is only here because ocaml insists that quotes in comments are closed.
           *)
          let find_include_file includepaths =
            (* build all possible filenames for the file we want to #include: *)
            let possiblepaths = (List.map (fun d -> concat d i) includepaths) in
            (* Rewrite all filenames in canonical form: *)
            let possiblepaths = List.map reduce_path possiblepaths in
            (* Remove duplicates: *)
            let possiblepaths = list_remove_dups possiblepaths in
            (* Remove filenames that don't exist: *)
            let possiblepaths = List.filter Sys.file_exists possiblepaths in
            match possiblepaths with
              [] -> error (Lexed (current_loc())) (Printf.sprintf "No such file '%s'." i)
            | [p] -> p
            | h::t ->
              (* The aggressive version that does not break examples: *)
              h
              (* The safest version: *)
              (* error (current_loc()) (Printf.sprintf "Cannot include file '%s' because multiple possible include paths are found." i) *)
          in
          let path = abs_path (find_include_file includepaths) in push_tlexer l path;
          let () =
            let pp1, last_macro_used1 = make_file_preprocessor reportMacroCall path p_macros p_ghost_macros (fun () -> !curr_tlexer#peek ()) (fun () -> !curr_tlexer#junk ()) p_in_ghost_range dataModel in
            pps := pp1::!pps;
            p_last_macro_used := last_macro_used1::!p_last_macro_used
          in
          let () =
            let macros = mk_macros0 () in
            let ghost_macros = Hashtbl.create 10 in
            cfp_macros := macros::!cfp_macros;
            cfp_ghost_macros := ghost_macros::!cfp_ghost_macros;
            let cfpp1, _ = make_file_preprocessor reportMacroCall path macros ghost_macros (fun () -> !curr_tlexer#peek ()) (fun () -> !curr_tlexer#junk ()) cfp_in_ghost_range dataModel in
            cfpps := cfpp1::!cfpps
          in
          if List.mem path !included_files then begin
            match p_next() with
            | Some (_, Eof) -> 
                let None = p_next () in
                if verbose = -1 then Printf.printf "%10.6fs: >>>> secondary include: %s\n" (Perf.time()) path;
                let None = cfp_next () in
                pop_pps ();
                (pop_tlexer(); Some(l, SecondaryInclude(i, path)))
            | Some _ -> let Lexed l = l in divergence l ("Preprocessor does not skip secondary inclusion of file \n" ^ path)
          end else begin
            if verbose = -1 then Printf.printf "%10.6fs: >>>> including file: %s\n" (Perf.time()) path;
            included_files := path::!included_files;
            Some (l,BeginInclude(kind, i, path))
          end
      | None ->
        if List.length !tlexers > 1 then begin
          if verbose = -1 then begin let path = List.hd !paths in Printf.printf "%10.6fs: >>>> end including file: %s\n" (Perf.time()) path end;
          let l = current_loc () in
          pop_pps ();
          pop_tlexer();
          Some (Lexed l, EndInclude)
        end else begin
          if verbose = -1 then Printf.printf "%10.6fs: >> finished preprocessing file: %s\n" (Perf.time()) path; 
          None
        end
      | _ -> p_t
      end
    end
    else begin
      match last_macro_used() with
        (l,m) -> divergence (current_loc ()) ("The C preprocessor and the context-free preprocessor produced different tokens. The expansion of a header cannot depend upon its context of defined macros (macro " ^ m ^ ")")
    end
  in
  let current_loc = ref dummy_loc in
  let next _ =
    let result = next_token () in
    begin match result with
      None -> ()
    | Some (l, t) -> current_loc := l
    end;
    result
  in
  ((fun () -> !current_loc), Stream.from next)

let make_sound_preprocessor reportMacroCall make_lexer path verbose include_paths dataModel define_macros =
  let included_files = ref [] in
  let ghost_macros = Hashtbl.create 10 in
  make_sound_preprocessor_core reportMacroCall make_lexer path verbose include_paths dataModel define_macros ghost_macros included_files


let make_preprocessor reportMacroCall make_lexer path verbose include_paths dataModel define_macros =
  make_sound_preprocessor reportMacroCall make_lexer path verbose include_paths dataModel define_macros
