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
      | c -> Printf.sprintf "%c" c::first_line_tokens (i + 1)
  and ident_token start i =
    match if i = n then None else Some text.[i] with
      Some ('A'..'Z'|'a'..'z'|'0'..'9'|'_') -> ident_token start (i + 1)
    | _ -> String.sub text start (i - start)::first_line_tokens i
  in
  first_line_tokens 0

type file_options = {file_opt_annot_char: char; file_opt_tab_size: int}

let get_file_options text =
  let tokens = get_first_line_tokens text in
  let rec iter annotChar tabSize toks =
    match toks with
      "verifast_annotation_char"::":"::c::toks when String.length c = 1 -> iter c.[0] tabSize toks
    | "tab_size"::":"::n::toks ->
      begin
        try
          iter annotChar (int_of_string n) toks
        with Failure "int_of_string" -> iter annotChar tabSize toks
      end
    | tok::toks -> iter annotChar tabSize toks
    | [] -> {file_opt_annot_char=annotChar; file_opt_tab_size=tabSize}
  in
  iter '@' 8 tokens

let readFile path =
  let chan, close_chan =
    if path = "<stdin>.c" || path = "<stdin>.java" then
      (stdin, fun _ -> ())  (* read file from standard input; used for the web interface *)
    else
      (open_in_bin path, close_in)
  in
  let count = ref 0 in
  let rec iter () =
    let buf = String.create 60000 in
    let result = input chan buf 0 60000 in
    count := !count + result;
    if result = 0 then [] else (buf, result)::iter()
  in
  let chunks = iter() in
  close_chan chan;
  let s = String.create !count in
  let rec iter2 chunks offset =
    match chunks with
      [] -> ()
    | (buf, size)::chunks ->
      String.blit buf 0 s offset size;
      iter2 chunks (offset + size)
  in
  iter2 chunks 0;
  file_to_utf8 s

type include_kind =
  DoubleQuoteInclude
| AngleBracketInclude

type token = (* ?token *)
  | Kwd of string
  | Ident of string
  | Int of big_int * bool (* true = decimal, false = hex or octal *) * bool (* true = suffix u or U *) * int_literal_lsuffix
  | RealToken of big_int  (* Tokens of the form 123r. Used to distinguish 1r/2, denoting one half, from 1/2, which evaluates to zero, in a context that does not require an expression of type 'real'. *)
  | RationalToken of num       (* Rational number literals. E.g. 0.5, 3.14, 3e8, 6.62607004E-34. Used for floating-point literals in real code, and for real number literals in annotations. Using the arbitrary-precision 'num' type instead of the OCaml 'float' type to avoid rounding errors. *)
  | String of string
  | AngleBracketString of string
  | CharToken of char
  | PreprocessorSymbol of string
  | BeginInclude of
      include_kind
      (** string of file included as written in the sourcecode, e.g. "../test.h" *)
      * string
      (** resolved filename of included file, e.g. "/home/jack/verifast-0.0/bin/stdio.h" *)
      * string
  | SecondaryInclude of
      (** Same as first string of BeginInclude *)
      string
      (** Same as first second string of BeginInclude *)
      * string
  | EndInclude
  | Eol
  | ErrorToken

let string_of_include_kind = function
  DoubleQuoteInclude -> "DoubleQuoteInclude"
| AngleBracketInclude -> "AngleBracketInclude"

let string_of_token t =
  begin match t with
    Kwd(s) -> "Keyword:" ^ s
  | Ident(s) -> "Identifier:" ^ s
  | Int(bi, dec, usuffix, lsuffix) ->
    "Int:" ^ Big_int.string_of_big_int bi ^
      (if usuffix then "U" else "") ^
      (match lsuffix with NoLSuffix -> "" | LSuffix -> "L" | LLSuffix -> "LL") ^
      (if dec then "(decimal)" else "(originally hex or octal)")
  | RealToken(bi) -> "RealToken:" ^ (Big_int.string_of_big_int bi)
  | RationalToken(n) -> "RationalToken:" ^ (Num.string_of_num n)
  | String(s) -> "String: " ^ s
  | CharToken(ch) -> "Char: " ^ (Char.escaped ch)
  | PreprocessorSymbol(s) -> "PPSymbol: " ^ s
  | BeginInclude(kind, s, _) -> "BeginInclude(" ^ string_of_include_kind kind ^ "): " ^ s
  | SecondaryInclude(s, _) -> "SecondaryInclude: " ^ s
  | EndInclude -> "EndInclude"
  | Eol -> "Eol"
  | _ -> "Error"
  end

(* necessary because e.g. for two Big_ints bi1 bi2, the comparison bi1 = bi2 is not allowed *)
let compare_tokens t1 t2 =
  begin match (t1,t2) with
    (None,None) -> true
  | (Some(_,Int(bi1,dec1,u1,l1)),Some(_,Int(bi2,dec2,u2,l2))) -> compare_big_int bi1 bi2 = 0 && (dec1,u1,l1) = (dec2,u2,l2)
  | (Some(_,RealToken(bi1)),Some(_,RealToken(bi2))) -> compare_big_int bi1 bi2 = 0
  | (Some(_,RationalToken(n1)),Some(_,RationalToken(n2))) -> Num.eq_num n1 n2
  | (Some(_,t1),Some(_,t2)) -> t1 = t2
  | _ -> false
end

exception ParseException of loc * string
let error l msg = raise (ParseException(l, msg))
exception PreprocessorDivergence of loc * string

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
  | DeclKind_InductiveType

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
let lexer_in_ghost_range = ref false

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
  let text_junk () = incr textpos; skip_backslashed_newlines () in
  
  let annotEnd = Printf.sprintf "%c*/" annotChar in
  
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

  let tokenpos = ref 0 in
  let token_srcpos = ref (path, !line, !textpos - !linepos + 1) in

  let current_srcpos() = (path, !line, !textpos - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in
  let error msg = error (current_loc()) msg in

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
      Not_found -> let n = String.length id in
      if n > 2 && id.[n - 2] = '_' && id.[n - 1] = 'H' then PreprocessorSymbol id else Ident id
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
        begin match text_peek () with
          '\'' -> text_junk (); Some (CharToken c)
        | _ -> error "Single quote expected."
        end
    | '"' ->
        if !in_include_directive then in_include_directive := false;
        start_token();
        text_junk ();
        reset_buffer (); Some (String (string ()))
    | '/' -> start_token(); text_junk (); maybe_comment ()
    | '\000' ->
      in_ghost_range := !ghost_range_start <> None;
      ghost_range_end();
      !stats#overhead ~path:path ~nonGhostLineCount:!non_ghost_line_count ~ghostLineCount:!ghost_line_count ~mixedLineCount:!mixed_line_count;
      None
    | '*' -> start_token(); text_junk(); begin match text_peek() with '=' -> text_junk(); Some (keyword_or_error "*=") | _ -> Some (keyword_or_error "*") end
    | c -> start_token(); text_junk (); Some (keyword_or_error (String.make 1 c))
  and ident () =
    match text_peek () with
      ('A'..'Z' | 'a'..'z' | '\128'..'\255' | '0'..'9' | '_' | '\'' | '$') as c ->
      text_junk (); store c; ident ()
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
          let str = get_string () in
          if (str.[0] = '0') then
            int_suffix (big_int_of_octal_string str) false
          else
            int_suffix (big_int_of_string str) true
        end
  and int_suffix value is_decimal =
    let cont usuffix lsuffix = Some (Int (value, is_decimal, usuffix, lsuffix)) in
    match text_peek () with
      'u'|'U' ->
      text_junk ();
      begin match text_peek () with
        'l'|'L' ->
        text_junk ();
        begin match text_peek () with
          'l'|'L' ->
          text_junk ();
          cont true LLSuffix
        | _ ->
          cont true LSuffix
        end
      | _ ->
        cont true NoLSuffix
      end
    | 'l'|'L' ->
      text_junk ();
      begin match text_peek () with
        'l'|'L' ->
        text_junk ();
        begin match text_peek () with
          'u'|'U' ->
          text_junk ();
          cont true LLSuffix
        | _ ->
          cont false LLSuffix
        end
      | 'u'|'U' ->
        text_junk ();
        cont true LSuffix
      | _ ->
        cont false LSuffix
      end
    | _ ->
      cont false NoLSuffix
  and hex_number () =
    match text_peek () with
      ('0'..'9' | 'A'..'F' | 'a'..'f') as c -> text_junk (); store c; hex_number ()
    | _ -> int_suffix (big_int_of_hex_string (get_string ())) false
  and decimal_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | _ -> Some (RationalToken (num_of_decimal_fraction (get_string ())))
  and exponent_part () =
    match text_peek () with
      ('+' | '-' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> end_exponent_part ()
  and end_exponent_part () =
    match text_peek () with
      ('0'..'9' as c) ->
        text_junk (); store c; end_exponent_part ()
    | _ -> Some (RationalToken (num_of_decimal_fraction (get_string ())))
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
          c when c = annotChar ->
          text_junk ();
          if !ghost_range_start <> None then raise Stream.Failure;
          ghost_range_start := Some !token_srcpos;
          reportRange GhostRangeDelimiter (current_loc());
          Some (Kwd "/*@")
        | '~' -> text_junk (); reportShouldFail (current_loc()); multiline_comment ()
        | _ -> multiline_comment ()
      )
    | '=' ->
      text_junk();
      Some (keyword_or_error "/=")
    | _ -> Some (keyword_or_error "/")
  and single_line_comment () =
    match text_peek () with
      '~' -> text_junk (); reportShouldFail (current_loc()); single_line_comment_rest ()
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
        let t = 
          match next_token () with
            Some t -> Some (current_loc(), t)
          | None -> None
        in 
        lexer_in_ghost_range := !ghost_range_start <> None; t
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
  let {file_opt_annot_char=annotChar} = get_file_options text in
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_helper keywords ghostKeywords path text reportRange false (match inGhostRange with None -> false | Some b -> b) true reportShouldFail annotChar in
  (loc, ignore_eol, token_stream)

(* The preprocessor *)

class type t_lexer =
  object
    method peek          : unit -> (loc * token) option
    method peekn         : int  -> ((loc * token) option) list
    method junk          : unit -> unit
    method push          : (loc * token) option -> unit
    method loc           : unit -> loc
    method ignore_eol    : unit -> bool
    method reset         : unit -> unit
    method commit        : unit -> unit
    method isGhostHeader : unit -> bool
  end

class tentative_lexer (lloc:unit -> loc) (lignore_eol:bool ref) (lstream:(loc * token) Stream.t) : t_lexer =
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
    method peekn(n) =
      if base + counter + n < fetched then
        Array.to_list (Array.sub buffer counter n)
      else begin
        this#fetch();
        this#peekn(n)
      end
    method junk() =
      counter <- counter + 1;
    method push(tok) =
      counter <- counter - 1;
      if (tok <> Array.get buffer (base + counter)) then
        raise (Stream.Error "Pushing incorrect token back into tentative lexer");
    method loc() =
      Array.get locs (base + counter)
    method ignore_eol() =
      !lignore_eol
    method reset() =
      counter_old <- counter;
      counter <- 0;
    method commit() =
      if counter <> counter_old then raise (PreprocessorDivergence (this#loc(), 
           "Different amount of tokens were consumed by normal and context-free preprocessors"));
      base <- base + counter;
      counter <- 0;
      counter_old <- 0;
    method isGhostHeader() =
      begin match this#peek() with 
        None -> false
      | Some (((f, _, _),_), _) -> Filename.check_suffix f ".gh"
      end
    
    method private fetch () =
      if fetched < (Array.length buffer) then begin
        Array.set buffer fetched (Stream.peek (lstream));
        Stream.junk lstream;
        Array.set locs (fetched + 1) (lloc());
        fetched <- fetched + 1;
      end else begin
        let length = 2 * (Array.length buffer) in
        let b = Array.make length None in
        let l = Array.make (length + 1) dummy_loc in
        Array.blit buffer 0 b 0 (Array.length buffer);
        Array.blit locs 0 l 0 (Array.length locs);
        buffer <- b;
        locs <- l;
        this#fetch();
      end
  end

let make_plugin_preprocessor plugin_begin_include plugin_end_include tlexer in_ghost_range =
  let macros = ref [Hashtbl.create 10] in
  let ghost_macros = ref [Hashtbl.create 10] in
  let get_macros () = if !in_ghost_range then !ghost_macros else !macros in
  let is_defined x =
    if Hashtbl.mem (List.hd !macros) x then 
      true
    else
      !in_ghost_range && Hashtbl.mem (List.hd !ghost_macros) x
  in
  let get_macro x =
    if is_defined x then
      if !in_ghost_range && Hashtbl.mem (List.hd !ghost_macros) x then
        Hashtbl.find (List.hd !ghost_macros) x
      else
        Hashtbl.find (List.hd !macros) x
    else
      (dummy_loc, None, [])
  in
  let last_macro_used = ref (dummy_loc, "") in
  let update_last_macro_used x =
    if is_defined x then begin
      match get_macro x with
        (l, _, _) -> last_macro_used := (l, x);
    end
  in
  let expanding_macro = ref false in
  let defining_macro = ref false in
  let is_concatenation_token t =
    match t with (_, Kwd "##") -> true | _ -> false
  in
  let streams = ref [] in
  let callers = ref [[]] in
  let push_list newCallers body =
    streams := Stream.of_list body::!streams;
    callers := (newCallers @ List.hd !callers)::!callers;
  in
  let pop_stream () =
    streams := List.tl !streams;
    callers := List.tl !callers;
  in
  let next_at_start_of_line = ref true in
  let ghost_range_delimiter_allowed = ref false in
  let peek () =
    let t = 
      match !streams with 
        s::_ -> Stream.peek s
      | [] -> !tlexer#peek()
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
    | [] -> !tlexer#junk()
  in
  let error msg = error (!tlexer#loc()) msg in
  let syntax_error () = error "Preprocessor syntax error" in
  let rec skip_block () =
    let at_start_of_line = !next_at_start_of_line in
    next_at_start_of_line := false;
    ghost_range_delimiter_allowed := true;
    match peek () with
      None -> ghost_range_delimiter_allowed := false
    | Some (_, Eol) -> junk (); next_at_start_of_line := true; skip_block ()
    | Some (_, Kwd "#") when at_start_of_line ->
      junk ();
      begin match peek () with
        Some (_, Kwd ("endif"|"else"|"elif")) -> ghost_range_delimiter_allowed := false
      | Some (_, Kwd ("ifdef"|"ifndef"|"if")) -> junk (); skip_branches (); skip_block ()
      | Some _ -> junk (); skip_block ()
      | None -> ghost_range_delimiter_allowed := false
      end
    | _ -> junk (); skip_block ()
  and skip_branches () =
    skip_block ();
    match peek () with
      None -> syntax_error ()
    | Some (_, Kwd "endif") -> junk (); ()
    | _ -> junk (); skip_branches ()
  in
  let rec skip_branch () =
    skip_block ();
    begin match peek () with
      Some (_, Kwd "endif") -> junk (); ()
    | Some (_, Kwd "elif") -> junk (); conditional ()
    | Some (_, Kwd "else") -> junk (); ()
    | None -> ()
    end
  and conditional () =
    let rec condition () =
      match peek () with
        None | Some (_, Eol) -> []
      | Some (l, Ident "defined") ->
        let check x = 
          let cond = 
            if is_defined x then begin
              update_last_macro_used x;
              (l, Int (unit_big_int, true, false, NoLSuffix))
            end
            else (l, Int (zero_big_int, true, false, NoLSuffix))
          in
          cond::condition ()
        in
        junk ();
        begin match peek () with
          Some (_, (Ident x | PreprocessorSymbol x)) ->
          junk ();
          check x
        | Some (_, Kwd "(") ->
          junk ();
          begin match peek () with
            Some (_, (Ident x | PreprocessorSymbol x)) ->
            junk ();
            begin match peek () with
              Some (_, Kwd ")") ->
              junk ();
              check x
            | _ -> syntax_error ()
            end
          | _ -> syntax_error ()
          end
        | _ -> syntax_error ()
        end
      | Some t -> junk (); t::condition ()
    in
    let condition = condition () in
    let condition = macro_expand [] condition in
    (* TODO: Support operators *)
    let isTrue =
      match condition with
        [(_, Int (n, _, _, _))] -> sign_big_int n <> 0
      | _ -> error "Operators in preprocessor conditions are not yet supported."
    in
    if isTrue then () else skip_branch ()
  and next_token () =
    let at_start_of_line = !next_at_start_of_line in
    next_at_start_of_line := false;
    match
      ghost_range_delimiter_allowed := true;
      let t = peek () in
      ghost_range_delimiter_allowed := false;
      t
    with
      None -> 
        if !streams = [] then begin
          let update_macros macros =
            match !macros with
              m1::m2::mrest -> macros := (plugin_end_include m1 m2)::mrest;
            | _ -> ()
          in
          update_macros macros;
          update_macros ghost_macros;
          if List.length !macros > 1 then
            next_token ()
          else
            None
        end
        else begin
          pop_stream ();
          if !expanding_macro then
            None
          else
            next_token ()
        end
    | Some t ->
    match t with
      (_, Eol) -> junk (); next_at_start_of_line := true; next_token ()
    | (l, Kwd "/*@") -> 
        if !tlexer#isGhostHeader() then raise (ParseException (l, "Ghost range delimiters are not allowed inside ghost headers."));
        junk (); in_ghost_range := true; 
        next_at_start_of_line := at_start_of_line; Some t
    | (l, Kwd "@*/") -> 
        if !tlexer#isGhostHeader() then raise (ParseException (l, "Ghost range delimiters are not allowed inside ghost headers."));
        junk (); in_ghost_range := false; 
        next_at_start_of_line := true; Some t
    | (l, Kwd "##") when !defining_macro -> Some t
    | (l, Kwd "#") when at_start_of_line ->
      junk ();
      begin match peek () with
      | None -> next_token ()
      | Some (l, Kwd "include") ->
        junk ();
        begin match peek () with
        | Some (l, (String s | AngleBracketString s as ss)) ->
          junk ();
          if List.mem s ["include_ignored_by_verifast.h"; "assert.h"; "limits.h"] then 
            next_token () 
          else begin
            if !tlexer#isGhostHeader() then
              if not (Filename.check_suffix s ".gh") then raise (ParseException (l, "#include directive in ghost header should specify a ghost header file (whose name ends in .gh)."))
            else begin
              if !in_ghost_range && not (Filename.check_suffix s ".gh") then raise (ParseException (l, "Ghost #include directive should specify a ghost header file (whose name ends in .gh)."));
              if not !in_ghost_range && (Filename.check_suffix s ".gh") then raise (ParseException (l, "Non-ghost #include directive should not specify a ghost header file."))
            end;
            macros := (plugin_begin_include (List.hd !macros))::!macros;
            ghost_macros := (plugin_begin_include (List.hd !ghost_macros))::!ghost_macros; 
            next_at_start_of_line := true;
            let includeKind = match ss with String _ -> DoubleQuoteInclude | AngleBracketString _ -> AngleBracketInclude in
            Some (!tlexer#loc(), BeginInclude(includeKind, s, ""))
          end
        | _ -> error "Filename expected"
        end
      | Some (l, Kwd "define") ->
        defining_macro := true;
        junk ();
        begin match peek () with
          Some (lx, Ident x) | Some (lx, PreprocessorSymbol x) ->
          junk ();
          let has_no_whitespace_between location1 location2 =
            let (start1, stop1) = location1 in
            let (path1, line1, col1) = stop1 in
            let (start2, stop2) = location2 in
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
              let params =
                match peek () with
                  Some (_, Kwd ")") -> junk (); []
                | Some (_, Ident x) | Some (_, PreprocessorSymbol x) ->
                  junk ();
                  let rec params () =
                    match peek () with
                      Some (_, Kwd ")") -> junk (); []
                    | Some (_, Kwd ",") ->
                      junk ();
                      begin match peek () with
                        Some (_, Ident x) | Some (_, PreprocessorSymbol x) -> junk (); x::params ()
                      | _ -> error "Macro parameter expected"
                      end
                    | _ -> error "Expected ',' for separating macro parameters or ')' for ending macro parameter list"
                  in
                  x::params ()
                | _ -> error "Macro definition syntax error"
              in
              Some params
            | _ -> None
          in
          let rec body () =
            match peek () with
              None | Some (_, Eol) -> []
            | Some t -> junk (); t::body ()
          in 
          let body = body () in
          Hashtbl.replace (List.hd (get_macros ())) x (lx, params, body);
          defining_macro := false;
          if ((List.length body) > 0) && 
               ((is_concatenation_token (List.hd body)) || 
                (is_concatenation_token (List.hd (List.rev body)))) then
            error "'##'-operator cannot appear at either end of a macro";
          next_token ()
        | _ -> error "Macro definition syntax error"
        end
      | Some (l, Kwd "undef") ->
        junk ();
        begin match peek () with
          Some (_, (Ident x | PreprocessorSymbol x)) ->
          junk ();
          Hashtbl.remove (List.hd (get_macros ())) x;
          next_token ()
        | _ -> syntax_error ()
        end
      | Some (l, Kwd ("ifdef"|"ifndef" as cond)) ->
        junk ();
        begin match peek () with
          Some (_, (Ident x | PreprocessorSymbol x)) ->
          junk ();
          update_last_macro_used x;
          if is_defined x <> (cond = "ifdef") then
            skip_branch ();
          next_token ()
        | _ -> syntax_error ()
        end
      | Some (l, Kwd "if") ->
        junk ();
        conditional ();
        next_token ()
      | Some (l, Kwd ("elif"|"else")) ->
        junk ();
        skip_branches ();
        next_token ()
      | Some (l, Kwd "endif") -> junk (); next_token ()
      | _ -> syntax_error ()
      end
    | (l, (Ident x|PreprocessorSymbol x)) as t when is_defined x && not (List.mem x (List.hd !callers)) ->
      update_last_macro_used x;
      junk ();
      let (_,params, body) = get_macro x in
      let concatenate tokens params args =
        let concat_tokens first second =
          let check_number ((_, _, c1), (_, _, c2)) i = 
            let number = (string_of_big_int i) in
            if lt_big_int i (big_int_of_int 0) || gt_big_int i (big_int_of_int 99) || 
                ((c2 - c1 - (String.length number)) <> 0) then
              (* This is necessary because the preceeding lexing fase translates literals like
                 0xFFFF way to decimal format, so we can not differentiate anymore. To ensure we 
                 are dealing wit a decimal literal without preceeding zeros, a very strict condition
                 is enforced here.
              *)
              error ("Unsupported use of concatenation operator in macro " ^
                     "(only decimal numbers i (0 <= i < 100) without leading zeros " ^ 
                     "are allowed for technical reasons)");
            number
          in
          let check_identifier x =
            if List.mem x params then
              let rec find_arg params args =
                match (params,args) with
                | (p::params, a::args) ->
                  begin
                    if p = x then
                      match a with
                      | [(l1, Ident id1)] -> id1;
                      | [(l1, Int (i1, _, _, _))] -> string_of_big_int i1;
                      | _ -> error "Unsupported use of concatenation operator in macro";
                    else
                      find_arg params args
                  end
                | _ -> error "Incorrect number of macro arguments"
              in
              find_arg params args
            else
              x
          in
          match first with
          | (l1, Ident id1) -> 
              begin
                match second with
                | (l2, Ident id2) -> (l2, Ident ((check_identifier id1) ^ (check_identifier id2)));
                | (l2, Int (i, _, _, _)) -> (l2, Ident ((check_identifier id1) ^ (check_number l2 i)))
                | _ -> error "Unsupported use of concatenation operator in macro";
              end
          | _ -> error "Unsupported use of concatenation operator in macro";
        in
        let rec concat_core tokens =
          match tokens with
          | t1::(_, Kwd "##")::t2::rest -> concat_core ((concat_tokens t1 t2)::rest)
          | t::rest -> t::(concat_core rest)
          | [] -> []
        in
        let result = concat_core tokens in
        if List.exists is_concatenation_token result
          then error "Invalid use of concatenation operator in macro";
        result
      in
      begin match params with
        None -> push_list [x] (concatenate body [] []); next_token ()
      | Some params ->
        match peek () with
          Some (_, Kwd "(") ->
          junk ();
          let args =
            let rec term parenDepth =
              match peek () with
                None -> syntax_error ()
              | Some ((_, Kwd ")") as t) -> junk (); t::if parenDepth = 1 then arg () else term (parenDepth - 1)
              | Some ((_, Kwd "(") as t) -> junk (); t::term (parenDepth + 1)
              | Some t -> junk (); t::term parenDepth
            and arg () =
              match peek () with
                Some (_, Kwd (")"|",")) -> []
              | Some (_, Kwd "(") -> term 0
              | None -> syntax_error ()
              | Some t -> junk (); t::arg ()
            in
            let rec args () =
              match peek () with
                Some (_, Kwd ")") -> junk (); []
              | Some (_, Kwd ",") -> junk (); let arg = arg () in arg::args ()
            in
            let arg = arg () in arg::args ()
          in
          let body =
            concatenate body params args
          in
          let args = List.map (macro_expand []) args in
          let bindings =
            match params, args with
              [], ([]|[[]]) -> []
            | _ ->
              match zip params args with
                None -> error "Incorrect number of macro arguments"
              | Some bs -> bs
          in
          let body =
            body |> flatmap begin function
              (_, (Ident x|PreprocessorSymbol x)) as t ->
              begin match try_assoc x bindings with
                None -> [t]
              | Some value -> value
              end
            | t -> [t]
            end
          in
          push_list [x] body; next_token ()
        | _ -> Some t
      end
    | t -> junk (); Some t
  and macro_expand newCallers tokens =
    let expending_macro_old = !expanding_macro in
    expanding_macro := true;
    let oldStreams = !streams in
    streams := [];
    push_list newCallers tokens;
    let rec get_tokens ts =
      match next_token () with
        None -> List.rev ts
      | Some t -> get_tokens (t::ts)
    in
    let ts = get_tokens [] in
    if expending_macro_old = false then expanding_macro := false;
    streams := oldStreams;
    ts
  in
  (next_token, fun _ -> !last_macro_used)

let make_sound_preprocessor make_lexer path verbose include_paths =
  if verbose = -1 then Printf.printf "%10.6fs: >> start preprocessing file: %s\n" (Perf.time()) path;
  let tlexers = ref [] in
  let curr_tlexer = ref (new tentative_lexer (fun () -> dummy_loc) (ref false) (Stream.of_list [])) in
  let is_ghost_header h = Filename.check_suffix h ".gh" in
  let p_in_ghost_range = ref [] in
  let cfp_in_ghost_range = ref [] in
  let included_files = ref [] in
  let paths = ref [] in  
  let push_tlexer path =
    p_in_ghost_range := (ref (is_ghost_header path))::!p_in_ghost_range;
    cfp_in_ghost_range := (ref (is_ghost_header path))::!cfp_in_ghost_range;
    let (loc, lexer_ignore_eol, stream) = make_lexer path include_paths ~inGhostRange:!(List.hd !p_in_ghost_range) in
    lexer_ignore_eol := false;
    curr_tlexer := new tentative_lexer loc lexer_ignore_eol stream;
    tlexers := !curr_tlexer::!tlexers;
    paths := path::!paths
  in
  let pop_tlexer () =
    p_in_ghost_range := List.tl !p_in_ghost_range;
    cfp_in_ghost_range := List.tl !cfp_in_ghost_range;
    tlexers := List.tl !tlexers;
    curr_tlexer := List.hd !tlexers;
    paths := List.tl !paths
  in
  push_tlexer path;
  let p_begin_include macros =
    macros
  in
  let p_end_include macros1 macros2 =
    macros1
  in
  let cfp_begin_include macros =
    Hashtbl.create 10
  in
  let cfp_end_include macros1 macros2 =
    Hashtbl.iter (fun k v -> Hashtbl.replace macros2 k v) macros1;
    macros2
  in
  let current_loc () = !curr_tlexer#loc() in
  let (p_next,last_macro_used) = make_plugin_preprocessor p_begin_include p_end_include curr_tlexer (List.hd !p_in_ghost_range) in
  let (cfp_next,_) = make_plugin_preprocessor cfp_begin_include cfp_end_include curr_tlexer (List.hd !cfp_in_ghost_range) in
  let divergence l s = 
    pop_tlexer();
    raise (PreprocessorDivergence (l , s))    
  in
  let rec next_token () =
    let p_t = p_next() in
    !curr_tlexer#reset();
    let cfp_t = cfp_next() in
    !curr_tlexer#commit();
    if (compare_tokens p_t cfp_t) && (!(List.hd !p_in_ghost_range) = !(List.hd !cfp_in_ghost_range)) then begin
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
              [] -> error (current_loc()) (Printf.sprintf "No such file '%s'." i)
            | [p] -> p
            | h::t ->
              (* The aggressive version that does not break examples: *)
              h
              (* The safest version: *)
              (* error (current_loc()) (Printf.sprintf "Cannot include file '%s' because multiple possible include paths are found." i) *)
          in
          let path = find_include_file includepaths in push_tlexer path;
          if List.mem path !included_files then begin
            match p_next() with
              Some _ -> divergence l ("Preprocessor does not skip secondary inclusion of file \n" ^ path)
            | None -> 
                if verbose = -1 then Printf.printf "%10.6fs: >>>> secondary include: %s\n" (Perf.time()) path;
                (* possible TODO: needs caching for more efficiency, but overhead is negligible *)
                let rec import_macros () =
                  match cfp_next() with 
                    Some _ -> import_macros ()
                  | None -> ()
                in
                import_macros ();
                (* end *)
                (pop_tlexer(); Some(l, SecondaryInclude(i, path)))
          end else begin
            if verbose = -1 then Printf.printf "%10.6fs: >>>> including file: %s\n" (Perf.time()) path;
            included_files := path::!included_files;
            Some (l,BeginInclude(kind, i, path))
          end;  
      | None -> if List.length !tlexers > 1 then begin 
                  if verbose = -1 then begin let path = List.hd !paths in Printf.printf "%10.6fs: >>>> end including file: %s\n" (Perf.time()) path end;
                  let l = current_loc () in pop_tlexer();
                  Some (l, EndInclude)
                end 
                else begin 
                  if verbose = -1 then Printf.printf "%10.6fs: >> finished preprocessing file: %s\n" (Perf.time()) path; 
                  None
                end
      | _ -> p_t
      end
    end
    else begin
      match last_macro_used() with
        (l,m) -> divergence l ("The expansion of a header (" ^ (string_of_loc (current_loc())) ^ ") cannot depend upon its context of defined macros (macro " ^ m ^ ")")
    end
  in
  ((fun () -> current_loc()), ref true, Stream.from (fun _ -> next_token ()))

let make_preprocessor make_lexer path verbose include_paths =
  make_sound_preprocessor make_lexer path verbose include_paths
