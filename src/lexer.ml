open Big_int
open Util
open Stats

(* Region: lexical analysis *)

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

type token = (* ?token *)
  | Kwd of string
  | Ident of string
  | Int of big_int
  | RealToken of big_int
  | Float of float
  | String of string
  | CharToken of char
  | PreprocessorSymbol of string
  | Eol
  | ErrorToken

(** Base path, relative path, line (1-based), column (1-based) *)
type srcpos = ((string * string) * int * int) (* ?srcpos *)

(** A range of source code: start position, end position *)
type loc = (srcpos * srcpos) (* ?loc *)

let dummy_srcpos = (("<nowhere>", "prelude"), 0, 0)
let dummy_loc = (dummy_srcpos, dummy_srcpos)

exception ParseException of loc * string

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
let make_lexer_core keywords ghostKeywords path text reportRange inComment inGhostRange exceptionOnError reportShouldFail annotChar =
  let textlength = String.length text in
  let textpos = ref 0 in
  let line = ref 1 in
  let linepos = ref 0 in
  
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
  let token_srcpos = ref (path, 1, 1) in

  let current_srcpos() = (path, !line, !textpos - !linepos + 1) in
  let current_loc() = (!token_srcpos, current_srcpos()) in

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

  let error msg =
      raise (Stream.Error msg)
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
      Not_found -> error "Illegal character"
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
    let new_line () =
      let old_linepos = !linepos in
      new_loc_line ();
      if !in_single_line_annotation then (
        in_single_line_annotation := false;
        let end_of_line = if 0 <= !textpos - 2 && text.[!textpos - 2] = '\r' && text.[!textpos - 1] = '\n' then !textpos - 2 else !textpos - 1 in
        ghost_range_end_at (path, !line - 1, end_of_line - old_linepos + 1); (* Do not include the newline in the ghost range; needed to make local syntax highlighting refresh hack work in vfide. *)
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
         ( reset_buffer (); Some (String (string ())) )
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
      stats#overhead ~path:path ~nonGhostLineCount:!non_ghost_line_count ~ghostLineCount:!ghost_line_count ~mixedLineCount:!mixed_line_count;
      None
    | '*' -> start_token(); text_junk(); begin match text_peek() with '=' -> text_junk(); Some (keyword_or_error "*=") | _ -> Some (keyword_or_error "*") end
    | c -> start_token(); text_junk (); Some (keyword_or_error (String.make 1 c))
  and ident () =
    match text_peek () with
      ('A'..'Z' | 'a'..'z' | '\128'..'\255' | '0'..'9' | '_' | '\'') as c ->
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
    | '.' ->
        text_junk (); store '.'; decimal_part ()
    | ('e' | 'E') ->
        text_junk (); store 'E'; exponent_part ()
    | ('r') ->
        text_junk (); Some (RealToken (big_int_of_string (get_string ())))
    | _ -> Some (Int (big_int_of_string (get_string ())))
  and hex_number () =
    match text_peek () with
      ('0'..'9' | 'A'..'F' | 'a'..'f') as c -> text_junk (); store c; hex_number ()
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
        match next_token () with
          Some t -> Some (current_loc(), t)
        | None -> None
      with
        Stream.Error msg when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      | Stream.Failure when not exceptionOnError -> reportRange ErrorRange (current_loc()); Some (current_loc(), ErrorToken)
      )),
   in_comment,
   in_ghost_range)

let make_lexer keywords ghostKeywords path text reportRange ?inGhostRange reportShouldFail =
  let {file_opt_annot_char=annotChar} = get_file_options text in
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_core keywords ghostKeywords path text reportRange false (match inGhostRange with None -> false | Some b -> b) true reportShouldFail annotChar in
  (loc, ignore_eol, token_stream)

(* The preprocessor *)

let make_preprocessor make_lexer basePath relPath include_paths =
  let macros = Hashtbl.create 10 in
  let streams = ref [] in
  let callers = ref [[]] in
  let paths = ref [] in
  let locs = ref [] in
  let loc = ref dummy_loc in
  let in_ghost_range = ref false in
  let push_lexer basePath relPath =
    let (loc, lexer_ignore_eol, stream) = make_lexer basePath relPath include_paths ~inGhostRange:!in_ghost_range in
    lexer_ignore_eol := false;
    streams := stream::!streams;
    callers := List.hd !callers::!callers;
    paths := (basePath, relPath)::!paths;
    locs := loc::!locs
  in
  let push_list newCallers body =
    streams := Stream.of_list body::!streams;
    callers := (newCallers @ List.hd !callers)::!callers;
    paths := List.hd !paths::!paths;
    locs := List.hd !locs::!locs
  in
  let pop_stream () =
    streams := List.tl !streams;
    callers := List.tl !callers;
    paths := List.tl !paths;
    locs := List.tl !locs
  in
  push_lexer basePath relPath;
  let pp_ignore_eol = ref true in
  let next_at_start_of_line = ref true in
  let peek () = loc := List.hd !locs (); Stream.peek (List.hd !streams) in
  let junk () = Stream.junk (List.hd !streams) in
  let error msg = raise (Stream.Error msg) in
  let syntax_error () = error "Preprocessor syntax error" in
  let rec skip_block () =
    let at_start_of_line = !next_at_start_of_line in
    next_at_start_of_line := false;
    match peek () with
      None -> ()
    | Some (_, Eol) -> junk (); next_at_start_of_line := true; skip_block ()
    | Some (_, Kwd "#") when at_start_of_line ->
      junk ();
      begin match peek () with
        Some (_, Kwd ("endif"|"else"|"elif")) -> ()
      | Some (_, Kwd ("ifdef"|"ifndef"|"if")) -> junk (); skip_branches (); skip_block ()
      | Some _ -> junk (); skip_block ()
      | None -> ()
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
        let check x = (if Hashtbl.mem macros x then (l, Int unit_big_int) else (l, Int zero_big_int))::condition () in
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
        [(_, Int n)] -> sign_big_int n <> 0
      | _ -> error "Operators in preprocessor conditions are not yet supported."
    in
    if isTrue then () else skip_branch ()
  and next_token () =
    let at_start_of_line = !next_at_start_of_line in
    next_at_start_of_line := false;
    match peek () with
      None -> pop_stream (); if !streams = [] then None else next_token ()
    | Some t ->
    match t with
      (_, Eol) -> junk (); next_at_start_of_line := true; next_token ()
    | (_, Kwd "/*@") -> junk (); in_ghost_range := true; next_at_start_of_line := at_start_of_line; Some t
    | (_, Kwd "@*/") -> junk (); in_ghost_range := false; Some t
    | (l, Kwd "#") when at_start_of_line ->
      junk ();
      begin match peek () with
      | None -> next_token ()
      | Some (l, Kwd "include") ->
        junk ();
        begin match peek () with
        | Some (l, String s) ->
          junk ();
          if List.mem s ["bool.h"; "assert.h"; "limits.h"] then next_token () else
          let basePath0, relPath0 = List.hd !paths in
          let rellocalpath = concat (Filename.dirname relPath0) s in
          let includepaths = List.append include_paths [basePath0; bindir] in
          let rec find_include_file includepaths =
            match includepaths with
              [] -> error (Printf.sprintf "No such file: '%s'" rellocalpath)
            | head::body ->
              let headerpath = concat head rellocalpath in
              if Sys.file_exists headerpath then
                (head, rellocalpath)
              else
                (find_include_file body)
          in
          let basePath, relPath = find_include_file includepaths in
          push_lexer basePath relPath;
          next_at_start_of_line := true;
          next_token ()
        | _ -> error "Filename expected"
        end
      | Some (l, Kwd "define") ->
        junk ();
        begin match peek () with
          Some (lx, Ident x) | Some (lx, PreprocessorSymbol x) ->
          junk ();
          let params =
            match peek () with
              Some (_, Kwd "(") ->
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
          Hashtbl.replace macros x (params, body);
          next_token ()
        | _ -> error "Macro definition syntax error"
        end
      | Some (l, Kwd "undef") ->
        junk ();
        begin match peek () with
          Some (_, (Ident x | PreprocessorSymbol x)) ->
          junk ();
          Hashtbl.remove macros x;
          next_token ()
        | _ -> syntax_error ()
        end
      | Some (l, Kwd ("ifdef"|"ifndef" as cond)) ->
        junk ();
        begin match peek () with
          Some (_, (Ident x | PreprocessorSymbol x)) ->
          junk ();
          if Hashtbl.mem macros x <> (cond = "ifdef") then
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
    | (l, (Ident x|PreprocessorSymbol x)) as t when Hashtbl.mem macros x && not (List.mem x (List.hd !callers)) ->
      junk ();
      let (params, body) = Hashtbl.find macros x in
      begin match params with
        None -> push_list [x] body; next_token ()
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
    let oldStreams = !streams in
    streams := [];
    push_list newCallers tokens;
    let rec get_tokens ts =
      match next_token () with
        None -> List.rev ts
      | Some t -> get_tokens (t::ts)
    in
    let ts = get_tokens [] in
    streams := oldStreams;
    ts
  in
  ((fun () -> !loc), pp_ignore_eol, Stream.from (fun _ -> next_token ()))
