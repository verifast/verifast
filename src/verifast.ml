(*

Welcome to the VeriFast codebase
================================

How to understand this codebase?

- This program is written in OCaml. Know OCaml.
  Read all docs at http://caml.inria.fr/.
  Familiarize yourself with the precedence of operators.
  Caveats:
  - Subexpression evaluation order is unspecified. Use let x = ... in ... to enforce ordering.
  - 'begin ... end' is alternative syntax for '(...)'. Coding guideline: use 'begin ... end' for multiline expressions.
  - 'if ... then ...; ...' parses as '(if ... then ...); ...'. To fix: 'if ... then begin ...; ... end'
  - OCaml supports structural equality 'x = y' (like 'equals' in Java) and reference equality 'x == y' (like '==' in Java).
    Similarly, 'x <> y' is structural inequality and 'x != y' is reference inequality.
  - All variables are immutable. For mutability, use ref cells. Ref cell assignment: 'x := y'; getting the value of a ref cell: '!x'.

- VeriFast uses OCaml lists extensively. Familiarize yourself with the List module. See library docs at http://caml.inria.fr.
  Additional list manipulation functions are defined at the top of this file. Familiarize yourself with them.

You can get an outline of this file in Notepad++ by copying the text
"Region:" to the clipboard and choosing TextFX->Viz->Hide Lines without (clipboard) text.
Get all lines back by choosing TextFX->Viz->Show Between-Selected or All-Reset Lines.

*)

open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)

(* Region: General-purpose utility functions *)

let num_of_ints p q = div_num (num_of_int p) (num_of_int q)

(** Same as fprintf followed by a flush. *)
let fprintff format = kfprintf (fun chan -> flush chan) format
(** Same as printf followed by a flush. *)
let printff format = fprintff stdout format

(** Keeps manifests produced by the compilation phase, for use during the linking phase. Avoids writing manifest files to disk. *)
let manifest_map: (string * string list) list ref = ref []
let jardeps_map: (string * string list) list ref = ref []

let option_map f x =
  match x with
    None -> None
  | Some x -> Some (f x)

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

(** Facilitates continuation-passing-style programming.
    For example, if you have a function 'foo x y cont', you can call it as follows: 'foo x y (fun z -> ...)'
    But if you nest the continuations deeply, you get lots of indentation and lots of parentheses at the end. The $. operator allows
    you to write this as follows:
    foo x y $. fun z ->
    foo x' y' $. fun z' ->
    ...
  *)
let ($.) f x = f x

(** Improves readability of list processing.
    Before:
    let xs' =
      List.map begin fun x ->
          ...
          ...
        end
        xs
     Notice that you have to go all the way to the end to find out which is list is being operated on.
     After:
     let xs' =
       xs |> List.map begin fun x ->
         ...
         ...
       end
  *)
let (|>) x f = f x

(** Like List.for_all2, except returns false if the lists have different length. *)
let rec for_all2 p xs ys =
  match (xs, ys) with
    ([], []) -> true
  | (x::xs, y::ys) -> p x y && for_all2 p xs ys
  | _ -> false

(** Same as [List.for_all2 f (take n xs) (take n ys)] *)
let for_all_take2 f n xs ys =
  let rec iter n xs ys =
    if n <= 0 then true else
    match (xs, ys) with
      (x::xs, y::ys) -> f x y && iter (n - 1) xs ys
  in
  iter n xs ys

(** Returns those elements of [xs] that also appear in [ys]. *)
let intersect xs ys = List.filter (fun x -> List.mem x ys) xs

(* Same as [List.concat (List.map f xs)], except perhaps slightly faster. *)
let rec flatmap (f: 'a -> 'b list) (xs: 'a list): 'b list =
  match xs with
    [] -> []
  | x::xs0 ->
    match f x with
      [] -> flatmap f xs0
    | ys -> ys @ flatmap f xs0

(** Returns the first element of [flatmap f xs], or None if there is none. Calls [f] only as many times as necessary. *)
let rec head_flatmap f xs =
  match xs with
    [] -> None
  | x::xs ->
    match f x with
      [] -> head_flatmap f xs
    | y::ys -> Some y

let rec head_flatmap_option f xs =
  match xs with
    [] -> None
  | x::xs ->
    match f x with
      None -> head_flatmap_option f xs
    | Some y as result -> result

(** Returns either None if f returns None for all elements of xs,
    or Some (y, xs0) where y is the value of f and xs0 is xs after removing the first element for which f returned Some _.
    Useful for extracting a chunk from a heap. *)
let extract (f: 'a -> 'b option) (xs: 'a list) =
  let rec iter xs' xs =
    match xs with
      [] -> None
    | x::xs ->
      match f x with
        None -> iter (x::xs') xs
      | Some y -> Some (y, xs'@xs)
  in
  iter [] xs

(** Drops the first n elements of xs *)
let rec drop n xs = if n = 0 then xs else drop (n - 1) (List.tl xs)

(** Takes the first n elements of xs *)
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

(** True if xs has no diplicates. *)
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

(** Same as [try_assoc], except returns the binding [(x, y)] instead of just [y]. *)
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

(** Like [List.map], except also passes the index of each element to f. *)
let imap (f: int -> 'a -> 'b) (xs: 'a list): 'b list =
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

let try_find p xs =
  try 
    Some(List.find p xs)
  with Not_found -> 
    None

let try_extract xs condition =
  let rec try_extract_core xs condition seen =
    match xs with
      [] -> None
    | x :: rest ->
      if condition x then
        Some((x, seen @ rest))
      else
        try_extract_core rest condition (seen @ [x])
  in
  try_extract_core xs condition []

let startswith s s0 =
  String.length s0 <= String.length s && String.sub s 0 (String.length s0) = s0

let chop_suffix s s0 =
  let n0 = String.length s0 in
  let n = String.length s in
  if n0 <= n && String.sub s (n - n0) n0 = s0 then Some (String.sub s 0 (n - n0)) else None

let chop_suffix_opt s s0 =
  match chop_suffix s s0 with None -> s | Some s -> s

(** Same as [try_assoc x (xys1 @ xys2)] but without performing the append operation. *)
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

let parsing_stopwatch = Stopwatch.create ()

class stats =
  object (self)
    val startTime = Perf.time()
    val startTicks = Stopwatch.processor_ticks()
    val mutable stmtsParsedCount = 0
    val mutable openParsedCount = 0
    val mutable closeParsedCount = 0
    val mutable stmtExecCount = 0
    val mutable execStepCount = 0
    val mutable branchCount = 0
    val mutable proverAssumeCount = 0
    val mutable definitelyEqualSameTermCount = 0
    val mutable definitelyEqualQueryCount = 0
    val mutable proverOtherQueryCount = 0
    val mutable proverStats = ""
    val mutable overhead: <path: string; nonghost_lines: int; ghost_lines: int; mixed_lines: int> list = []
    val mutable functionTimings: (string * float) list = []
    
    method tickLength = let t1 = Perf.time() in let ticks1 = Stopwatch.processor_ticks() in (t1 -. startTime) /. Int64.to_float (Int64.sub ticks1 startTicks)
    
    method stmtParsed = stmtsParsedCount <- stmtsParsedCount + 1
    method openParsed = openParsedCount <- openParsedCount + 1
    method closeParsed = closeParsedCount <- closeParsedCount + 1
    method stmtExec = stmtExecCount <- stmtExecCount + 1
    method execStep = execStepCount <- execStepCount + 1
    method branch = branchCount <- branchCount + 1
    method proverAssume = proverAssumeCount <- proverAssumeCount + 1
    method definitelyEqualSameTerm = definitelyEqualSameTermCount <- definitelyEqualSameTermCount + 1
    method definitelyEqualQuery = definitelyEqualQueryCount <- definitelyEqualQueryCount + 1
    method proverOtherQuery = proverOtherQueryCount <- proverOtherQueryCount + 1
    method appendProverStats (text, tickCounts) =
      let tickLength = self#tickLength in
      proverStats <- proverStats ^ text ^ String.concat "" (List.map (fun (lbl, ticks) -> Printf.sprintf "%s: %.6fs\n" lbl (Int64.to_float ticks *. tickLength)) tickCounts)
    method overhead ~path ~nonGhostLineCount ~ghostLineCount ~mixedLineCount =
      let (basepath, relpath) = path in
      let path = Filename.concat basepath relpath in
      let o = object method path = path method nonghost_lines = nonGhostLineCount method ghost_lines = ghostLineCount method mixed_lines = mixedLineCount end in
      overhead <- o::overhead
    method recordFunctionTiming funName seconds = if seconds > 0.1 then functionTimings <- (funName, seconds)::functionTimings
    method getFunctionTimings =
      let compare (_, t1) (_, t2) = compare t1 t2 in
      let timingsSorted = List.sort compare functionTimings in
      let max_funName_length = List.fold_left (fun m (n, _) -> max m (String.length n)) 0 timingsSorted in
      String.concat "" (List.map (fun (funName, seconds) -> Printf.sprintf "  %-*s: %6.2f seconds\n" max_funName_length funName seconds) timingsSorted)
    
    method printStats =
      print_endline ("Syntactic annotation overhead statistics:");
      let max_path_size = List.fold_left (fun m o -> max m (String.length o#path)) 0 overhead in
      List.iter
        begin fun o ->
          let overhead = float_of_int (o#ghost_lines + o#mixed_lines) *. 100.0 /. float_of_int o#nonghost_lines in
          Printf.printf "  %-*s: lines: code: %4d; annot: %4d; mixed: %4d; overhead: %4.0f%%\n"
            max_path_size o#path o#nonghost_lines o#ghost_lines o#mixed_lines overhead
        end
        overhead;
      print_endline ("Statements parsed: " ^ string_of_int stmtsParsedCount);
      print_endline ("Open statements parsed: " ^ string_of_int openParsedCount);
      print_endline ("Close statements parsed: " ^ string_of_int closeParsedCount);
      print_endline ("Statement executions: " ^ string_of_int stmtExecCount);
      print_endline ("Execution steps (including assertion production/consumption steps): " ^ string_of_int execStepCount);
      print_endline ("Symbolic execution forks: " ^ string_of_int branchCount);
      print_endline ("Prover assumes: " ^ string_of_int proverAssumeCount);
      print_endline ("Term equality tests -- same term: " ^ string_of_int definitelyEqualSameTermCount);
      print_endline ("Term equality tests -- prover query: " ^ string_of_int definitelyEqualQueryCount);
      print_endline ("Term equality tests -- total: " ^ string_of_int (definitelyEqualSameTermCount + definitelyEqualQueryCount));
      print_endline ("Other prover queries: " ^ string_of_int proverOtherQueryCount);
      print_endline ("Prover statistics:\n" ^ proverStats);
      Printf.printf "Time spent parsing: %.6fs\n" (Int64.to_float (Stopwatch.ticks parsing_stopwatch) *. self#tickLength);
      print_endline ("Function timings (> 0.1s):\n" ^ self#getFunctionTimings);
      print_endline (Printf.sprintf "Total time: %.2f seconds" (Perf.time() -. startTime))
  end

let stats = new stats

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
  let chan = open_in_bin path in
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
    | ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '=' | '>' |
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

let make_lexer keywords ghostKeywords path text reportRange reportShouldFail =
  let {file_opt_annot_char=annotChar} = get_file_options text in
  let (loc, ignore_eol, token_stream, _, _) = make_lexer_core keywords ghostKeywords path text reportRange false false true reportShouldFail annotChar in
  (loc, ignore_eol, token_stream)

(* The preprocessor *)

let make_preprocessor make_lexer basePath relPath =
  let macros = Hashtbl.create 10 in
  let streams = ref [] in
  let callers = ref [[]] in
  let paths = ref [] in
  let locs = ref [] in
  let loc = ref dummy_loc in
  let push_lexer basePath relPath =
    let (loc, lexer_ignore_eol, stream) = make_lexer basePath relPath in
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
  let basePath, relPath = (), () in (* Hide the variables *)
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
          let localRelPath = Filename.concat (Filename.dirname relPath0) s in
          let basePath, relPath =
            if Sys.file_exists (Filename.concat basePath0 localRelPath) then
              basePath0, localRelPath
            else
              let sysPath = Filename.concat bindir s in
              if Sys.file_exists sysPath then
                bindir, s
              else
                error "No such file"
          in
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
              | Some ((_, Kwd "(") as t) -> term 0
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

(* Some types for dealing with constants *)

type constant_value = (* ?constant_value *)
  IntConst of big_int
| BoolConst of bool
| StringConst of string
| NullConst

exception NotAConstant

(* Region: ASTs *)

type type_ = (* ?type_ *)
    Bool
  | Void
  | IntType
  | UShortType
  | ShortType
  | UintPtrType  (* The uintptr_t type from the C99 standard. It's an integer type big enough to hold a pointer value. *)
  | RealType
  | UChar
  | Char
  | StructType of string
  | PtrType of type_
  | FuncType of string   (* The name of a typedef whose body is a C function type. *)
  | InductiveType of string * type_ list
  | PredType of string list * type_ list * int option (* if None, not necessarily precise; if Some n, precise with n input parameters *)
  | PureFuncType of type_ * type_  (* Curried *)
  | ObjType of string
  | ArrayType of type_
  | StaticArrayType of type_ * int (* for array declarations in C *)
  | BoxIdType (* box type, for shared boxes *)
  | HandleIdType (* handle type, for shared boxes *)
  | AnyType (* supertype of all inductive datatypes; useful in combination with predicate families *)
  | TypeParam of string (* a reference to a type parameter declared in the enclosing datatype/function/predicate *)
  | InferredType of type_ option ref (* inferred type, is unified during type checking *)
  | ClassOrInterfaceName of string (* not a real type; used only during type checking *)
  | PackageName of string (* not a real type; used only during type checking *)
  | RefType of type_ (* not a real type; used only for locals whose address is taken *)
  | PluginInternalType of DynType.dyn

type prover_type = ProverInt | ProverBool | ProverReal | ProverInductive (* ?prover_type *)

(** Types as they appear in source code, before validity checking and resolution. *)
type type_expr = (* ?type_expr *)
    StructTypeExpr of loc * string
  | PtrTypeExpr of loc * type_expr
  | ArrayTypeExpr of loc * type_expr
  | StaticArrayTypeExpr of loc * type_expr (* type *) * int (* number of elements*)
  | ManifestTypeExpr of loc * type_  (* A type expression that is obviously a given type. *)
  | IdentTypeExpr of loc * string option (* package name *) * string
  | ConstructedTypeExpr of loc * string * type_expr list  (* A type of the form x<T1, T2, ...> *)
  | PredTypeExpr of loc * type_expr list * int option (* if None, not necessarily precise; if Some n, precise with n input parameters *)
  | PureFuncTypeExpr of loc * type_expr list   (* Potentially uncurried *)

(** An object used in predicate assertion ASTs. Created by the parser and filled in by the type checker.
    TODO: Since the type checker now generates a new AST anyway, we can eliminate this hack. *)
class predref (name: string) = (* ?predref *)
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
  ident_scope = (* ?ident_scope *)
    LocalVar
  | PureCtor
  | FuncName
  | PredFamName
  | EnumElemName of big_int
  | GlobalName
  | ModuleName
  | PureFuncName

type
  operator =  (* ?operator *)
  | Add | Sub | Le | Lt | Eq | Neq | And | Or | Xor | Not | Mul | Div | Mod | BitNot | BitAnd | BitXor | BitOr | ShiftLeft | ShiftRight
and
  expr = (* ?expr *)
    True of loc
  | False of loc
  | Null of loc
  | Var of loc * string * ident_scope option ref  (* An identifier. *)
  | Operation of (* voor operaties met bovenstaande operators*)
      loc *
      operator *
      expr list *
      type_ list option ref
  | IntLit of loc * big_int * type_ option ref (* int literal*)
  | RealLit of loc * num
  | StringLit of loc * string (* string literal *)
  | ClassLit of loc * string (* class literal in java *)
  | Read of loc * expr * string (* lezen van een veld; hergebruiken voor java field access *)
  | ArrayLengthExpr of loc * expr
  | WRead of
      loc *
      expr *
      string (* parent *) *
      string (* field name *) *
      type_ (* range *) *
      bool (* static *) *
      constant_value option option ref *
      ghostness
  | ReadArray of loc * expr * expr
  | WReadArray of loc * expr * type_ * expr
  | Deref of loc * expr * type_ option ref (* pointee type *) (* pointer dereference *)
  | CallExpr of (* oproep van functie/methode/lemma/fixpoint *)
      loc *
      string *
      type_expr list (* type arguments *) *
      pat list (* indices, in case this is really a predicate assertion *) *
      pat list (* arguments *) *
      method_binding
  | ExprCallExpr of (* Call whose callee is an expression instead of a plain identifier *)
      loc *
      expr *
      expr list
  | WFunPtrCall of loc * string * expr list
  | WPureFunCall of loc * string * type_ list * expr list
  | WPureFunValueCall of loc * expr * expr list
  | WFunCall of loc * string * type_ list * expr list
  | WMethodCall of
      loc *
      string (* declaring class or interface *) *
      string (* method name *) *
      type_ list (* parameter types (not including receiver) *) *
      expr list (* args, including receiver if instance method *) *
      method_binding
  | NewArray of loc * type_expr * expr
  | NewObject of loc * string * expr list
  | NewArrayWithInitializer of loc * type_expr * expr list
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of
      loc *
      expr *
      switch_expr_clause list *
      (loc * expr) option * (* default clause *)
      (type_ * (string * type_) list * type_ list * type_) option ref (* used during evaluation when generating an anonymous fixpoint function, to get the prover types right *)
  | PredNameExpr of loc * string (* naam van predicaat en line of code*)
  | CastExpr of loc * bool (* truncating *) * type_expr * expr (* cast *)
  | Upcast of expr * type_ (* from *) * type_ (* to *)  (* Not generated by the parser; inserted by the typechecker. Required to prevent bad downcasts during autoclose. *)
  | WidenedParameterArgument of expr (* Appears only as part of LitPat (WidenedParameterArgument e). Indicates that the predicate parameter is considered to range over a larger set (e.g. Object instead of class C). *)
  | SizeofExpr of loc * type_expr
  | AddressOf of loc * expr
  | ProverTypeConversion of prover_type * prover_type * expr  (* Generated during type checking in the presence of type parameters, to get the prover types right *)
  | ArrayTypeExpr' of loc * expr (* horrible hack --- for well-formed programs, this exists only during parsing *)
  | AssignExpr of loc * expr * expr
  | AssignOpExpr of loc * expr * operator * expr * bool (* true = return value of lhs before operation *) * type_ list option ref * type_ option ref
  | InstanceOfExpr of loc * expr * type_expr
  | SuperMethodCall of loc * string * expr list
  | WSuperMethodCall of loc * string * expr list * (loc * ghostness * (type_ option) * (string * type_) list * asn * asn * ((type_ * asn) list) * visibility)
  | InitializerList of loc * expr list
and
  pat = (* ?pat *)
    LitPat of expr (* literal pattern *)
  | VarPat of string (* var pattern, aangeduid met ? in code *)
  | DummyPat (*dummy pattern, aangeduid met _ in code *)
and
  switch_expr_clause = (* ?switch_expr_clause *)
    SwitchExprClause of loc * string * string list * expr (* switch uitdrukking *)
and
  language = (* ?language *)
    Java
  | CLang
and
  method_binding = (* ?method_binding *)
    Static
  | Instance
and
  visibility = (* ?visibility *)
    Public
  | Protected
  | Private
  | Package
and
  package = (* ?package *)
    PackageDecl of loc * string * import list * decl list
and
  import = (* ?import *)
    Import of
        loc *
        string *
        string option (* None betekent heel package, Some string betekent 1 ding eruit *)
and
  stmt = (* ?stmt *)
    PureStmt of (* Statement of the form /*@ ... @*/ *)
        loc *
        stmt
  | NonpureStmt of (* Nested non-pure statement; used for perform_action statements on shared boxes. *)
      loc *
      bool (* allowed *) *
      stmt
  | DeclStmt of (* enkel declaratie *)
      loc *
      (loc * type_expr * string * expr option * bool ref (* indicates whether address is taken *)) list
  | ExprStmt of expr
  | IfStmt of (* if  regel-conditie-branch1-branch2  *)
      loc *
      expr *
      stmt list *
      stmt list
  | SwitchStmt of (* switch over inductief type regel-expr- constructor)*)
      loc *
      expr *
      switch_stmt_clause list
  | Assert of loc * asn (* assert regel-predicate *)
  | Leak of loc * asn (* expliciet lekken van assertie, nuttig op einde van thread*)
  | Open of
      loc *
      expr option *  (* Target object *)
      string *
      type_expr list *  (* Type arguments *)
      pat list *  (* Indices for predicate family instance, or constructor arguments for predicate constructor *)
      pat list *  (* Arguments *)
      pat option  (* Coefficient for fractional permission *)
  | Close of
      loc *
      expr option *
      string *
      type_expr list *
      pat list *
      pat list *
      pat option
  | ReturnStmt of loc * expr option (*return regel-return value (optie) *)
  | WhileStmt of
      loc *
      expr *
      loop_spec option *
      expr option * (* decreases clause *)
      stmt list
  | BlockStmt of
      loc *
      decl list *
      stmt list *
      loc *
      string list ref
  | PerformActionStmt of
      loc *
      bool ref (* in non-pure context *) *
      string *
      pat list *
      loc *
      string *
      pat list *
      loc *
      string *
      expr list *
      stmt list *
      loc (* close brace of body *) *
      (loc * expr list) option *
      loc *
      string *
      expr list
  | SplitFractionStmt of (* split_fraction ... by ... *)
      loc *
      string *
      type_expr list *
      pat list *
      expr option
  | MergeFractionsStmt of (* merge_fraction ...*)
      loc *
      string *
      type_expr list *
      pat list
  | CreateBoxStmt of
      loc *
      string *
      string *
      expr list *
      (loc * string * string * expr list) list (* and_handle clauses *)
  | CreateHandleStmt of
      loc *
      string *
      string *
      expr
  | DisposeBoxStmt of
      loc *
      string *
      pat list *
      (loc * string * pat list) list (* and_handle clauses *)
  | LabelStmt of loc * string
  | GotoStmt of loc * string
  | NoopStmt of loc
  | InvariantStmt of
      loc *
      asn (* join point *)
  | ProduceLemmaFunctionPointerChunkStmt of
      loc *
      expr *
      (string * type_expr list * expr list * (loc * string) list * loc * stmt list * loc) option *
      stmt option
  | ProduceFunctionPointerChunkStmt of
      loc *
      string *
      expr *
      expr list *
      (loc * string) list *
      loc *
      stmt list *
      loc
  | Throw of loc * expr
  | TryCatch of
      loc *
      stmt list *
      (loc * type_expr * string * stmt list) list
  | TryFinally of
      loc *
      stmt list *
      loc *
      stmt list
  | Break of loc
  | SuperConstructorCall of loc * expr list
and
  loop_spec = (* ?loop_spec *)
  | LoopInv of asn
  | LoopSpec of asn * asn
and
  switch_stmt_clause = (* ?switch_stmt_clause *)
  | SwitchStmtClause of loc * expr * stmt list
  | SwitchStmtDefaultClause of loc * stmt list
and
  asn = (* A separation logic assertion *) (* ?asn *)
    PointsTo of (* toegang tot veld regel-expr-veld-pattern *)
        loc *
        expr *
        pat
  | WPointsTo of
      loc *
      expr *
      type_ *
      pat
  | PredAsn of (* Predicate assertion, before type checking *)
      loc *
      predref *
      type_expr list *
      pat list (* indices of predicate family instance *) *
      pat list
  | WPredAsn of (* Predicate assertion, after type checking. (W is for well-formed) *)
      loc *
      predref *
      bool * (* prefref refers to global name *)
      type_ list *
      pat list *
      pat list
  | InstPredAsn of
      loc *
      expr *
      string *
      expr * (* index *)
      pat list
  | WInstPredAsn of
      loc *
      expr option *
      string (* static type *) *
      class_finality (* finality of static type *) *
      string (* family type *) *
      string *
      expr (* index *) *
      pat list
  | ExprAsn of (* uitdrukking regel-expr *)
      loc *
      expr
  | Sep of (* separate conjunction *)
      loc *
      asn *
      asn
  | IfAsn of (* if-predicate in de vorm expr? p1:p2 regel-expr-p1-p2 *)
      loc *
      expr *
      asn *
      asn
  | SwitchAsn of (* switch over cons van inductive type regel-expr-clauses*)
      loc *
      expr *
      switch_asn_clause list
  | WSwitchAsn of (* switch over cons van inductive type regel-expr-clauses*)
      loc *
      expr *
      string * (* inductive type (fully qualified) *)
      switch_asn_clause list
  | EmpAsn of  (* als "emp" bij requires/ensures staat -regel-*)
      loc
  | CoefAsn of (* fractional permission met coeff-predicate*)
      loc *
      pat *
      asn
  | PluginAsn of loc * string
  | WPluginAsn of loc * string list * Plugins.typechecked_plugin_assertion
and
  switch_asn_clause = (* ?switch_asn_clause *)
  | SwitchAsnClause of
      loc * 
      string * 
      string list * 
      prover_type option list option ref (* Boxing info *) *
      asn (* clauses bij switch  regel-cons-lijst v var in cons-body *)
and
  func_kind = (* ?func_kind *)
  | Regular
  | Fixpoint
  | Lemma of bool (* indicates whether an axiom should be generated for this lemma *) * expr option (* trigger *)
and
  meth = (* ?meth *)
  | Meth of
      loc * 
      ghostness * 
      type_expr option * 
      string * 
      (type_expr * string) list * 
      (asn * asn * ((type_expr * asn) list)) option * 
      (stmt list * loc (* Close brace *)) option * 
      method_binding * 
      visibility *
      bool (* is declared abstract? *)
and
  cons = (* ?cons *)
  | Cons of
      loc * 
      (type_expr * string) list * 
      (asn * asn * ((type_expr * asn) list)) option * 
      (stmt list * loc (* Close brace *)) option * 
      visibility
and
  instance_pred_decl = (* ?instance_pred_decl *)
  | InstancePredDecl of loc * string * (type_expr * string) list * asn option
and
  class_finality =
  | FinalClass
  | ExtensibleClass
and
  decl = (* ?decl *)
    Struct of loc * string * field list option
  | Inductive of  (* inductief data type regel-naam-type parameters-lijst van constructors*)
      loc *
      string *
      string list *
      ctor list
  | Class of
      loc *
      bool (* abstract *) *
      class_finality *
      string *
      meth list *
      field list *
      cons list *
      string (* superclass *) *
      string list (* itfs *) *
      instance_pred_decl list
  | Interface of 
      loc *
      string *
      string list *
      field list *
      meth list *
      instance_pred_decl list
  | PredFamilyDecl of
      loc *
      string *
      string list (* type parameters *) *
      int (* number of indices *) *
      type_expr list *
      int option (* (Some n) means the predicate is precise and the first n parameters are input parameters *)
  | PredFamilyInstanceDecl of
      loc *
      string *
      string list (* type parameters *) *
      (loc * string) list *
      (type_expr * string) list *
      asn
  | PredCtorDecl of
      loc *
      string *
      (type_expr * string) list *
      (type_expr * string) list *
      asn
  | Func of
      loc *
      func_kind *
      string list *  (* type parameters *)
      type_expr option *  (* return type *)
      string *  (* name *)
      (type_expr * string) list *  (* parameters *)
      bool (* nonghost_callers_only *) *
      (string * type_expr list * (loc * string) list) option (* implemented function type, with function type type arguments and function type arguments *) *
      (asn * asn) option *  (* contract *)
      (stmt list * loc (* Close brace *)) option *  (* body *)
      method_binding *  (* static or instance *)
      visibility
  | TypedefDecl of
      loc *
      type_expr *
      string
  | FuncTypeDecl of
      loc *
      ghostness *
      type_expr option *
      string *
      string list *
      (type_expr * string) list *
      (type_expr * string) list *
      (asn * asn)
  | BoxClassDecl of
      loc *
      string *
      (type_expr * string) list *
      asn *
      action_decl list *
      handle_pred_decl list
  (* enum def met line - name - elements *)
  | EnumDecl of loc * string * (string * expr option) list
  | Global of loc * type_expr * string * expr option
  | UnloadableModuleDecl of loc
  | LoadPluginDecl of loc * loc * string
and (* shared box is deeltje ghost state, waarde kan enkel via actions gewijzigd worden, handle predicates geven info over de ghost state, zelfs als er geen eigendom over de box is*)
  action_decl = (* ?action_decl *)
  | ActionDecl of loc * string * (type_expr * string) list * expr * expr
and (* action, kan value van shared box wijzigen*)
  handle_pred_decl = (* ?handle_pred_decl *)
  | HandlePredDecl of loc * string * (type_expr * string) list * expr * preserved_by_clause list
and (* handle predicate geeft info over ghost state van shared box, zelfs als er geen volledige eigendom is vd box*)
  preserved_by_clause = (* ?preserved_by_clause *)
  | PreservedByClause of loc * string * string list * stmt list
and
  ghostness = (* ?ghostness *)
  | Ghost
  | Real
and
  field =
  | Field of (* ?field *)
      loc *
      ghostness *
      type_expr *
      string (* name of the field *) *
      method_binding *
      visibility *
      bool (* final *) *
      expr option
and
  ctor = (* ?ctor *)
  | Ctor of loc * string * type_expr list (* constructor met regel-naam-lijst v types v args*)
and
  member = (* ?member *)
  | FieldMember of field list
  | MethMember of meth
  | ConsMember of cons
  | PredMember of instance_pred_decl

let func_kind_of_ghostness gh =
  match gh with
    Real -> Regular
  | Ghost -> Lemma (false, None)
  
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
  
let string_of_srcpos (p,l,c) = p ^ "(" ^ string_of_int l ^ "," ^ string_of_int c ^ ")"

let string_of_path (basedir, relpath) = Filename.concat basedir relpath

let string_of_loc ((p1, l1, c1), (p2, l2, c2)) =
  string_of_path p1 ^ "(" ^ string_of_int l1 ^ "," ^ string_of_int c1 ^
  if p1 = p2 then
    if l1 = l2 then
      if c1 = c2 then
        ")"
      else
        "-" ^ string_of_int c2 ^ ")"
    else
      "-" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"
  else
    ")-" ^ string_of_path p2 ^ "(" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"
let string_of_func_kind f=
  match f with
    Lemma(_) -> "lemma"
  | Regular -> "regular"
  | Fixpoint -> "fixpoint"
let tostring f=
  match f with
  Instance -> "instance"
  | Static -> "static"
let rec expr_loc e =
  match e with
    True l -> l
  | False l -> l
  | Null l -> l
  | Var (l, x, _) -> l
  | IntLit (l, n, t) -> l
  | RealLit (l, n) -> l
  | StringLit (l, s) -> l
  | ClassLit (l, s) -> l
  | Operation (l, op, es, ts) -> l
  | Read (l, e, f) -> l
  | ArrayLengthExpr (l, e) -> l
  | WRead (l, _, _, _, _, _, _, _) -> l
  | ReadArray (l, _, _) -> l
  | WReadArray (l, _, _, _) -> l
  | Deref (l, e, t) -> l
  | CallExpr (l, g, targs, pats0, pats,_) -> l
  | ExprCallExpr (l, e, es) -> l
  | WPureFunCall (l, g, targs, args) -> l
  | WPureFunValueCall (l, e, es) -> l
  | WFunPtrCall (l, g, args) -> l
  | WFunCall (l, g, targs, args) -> l
  | WMethodCall (l, tn, m, pts, args, fb) -> l
  | NewObject (l, cn, args) -> l
  | NewArray(l, _, _) -> l
  | NewArrayWithInitializer (l, _, _) -> l
  | IfExpr (l, e1, e2, e3) -> l
  | SwitchExpr (l, e, secs, _, _) -> l
  | SizeofExpr (l, t) -> l
  | PredNameExpr (l, g) -> l
  | CastExpr (l, trunc, te, e) -> l
  | Upcast (e, fromType, toType) -> expr_loc e
  | WidenedParameterArgument e -> expr_loc e
  | AddressOf (l, e) -> l
  | ArrayTypeExpr' (l, e) -> l
  | AssignExpr (l, lhs, rhs) -> l
  | AssignOpExpr (l, lhs, op, rhs, postOp, _, _) -> l
  | ProverTypeConversion (t1, t2, e) -> expr_loc e
  | InstanceOfExpr(l, e, tp) -> l
  | SuperMethodCall(l, _, _) -> l
  | WSuperMethodCall(l, _, _, _) -> l
  | InitializerList (l, _) -> l

let asn_loc p =
  match p with
    PointsTo (l, e, rhs) -> l
  | WPointsTo (l, e, tp, rhs) -> l
  | PredAsn (l, g, targs, ies, es) -> l
  | WPredAsn (l, g, _, targs, ies, es) -> l
  | InstPredAsn (l, e, g, index, pats) -> l
  | WInstPredAsn (l, e_opt, tns, cfin, tn, g, index, pats) -> l
  | ExprAsn (l, e) -> l
  | Sep (l, p1, p2) -> l
  | IfAsn (l, e, p1, p2) -> l
  | SwitchAsn (l, e, sacs) -> l
  | WSwitchAsn (l, e, i, sacs) -> l
  | EmpAsn l -> l
  | CoefAsn (l, coef, body) -> l
  | PluginAsn (l, asn) -> l
  | WPluginAsn (l, xs, asn) -> l
  
let stmt_loc s =
  match s with
    PureStmt (l, _) -> l
  | NonpureStmt (l, _, _) -> l
  | ExprStmt e -> expr_loc e
  | DeclStmt (l, _) -> l
  | IfStmt (l, _, _, _) -> l
  | SwitchStmt (l, _, _) -> l
  | Assert (l, _) -> l
  | Leak (l, _) -> l
  | Open (l, _, _, _, _, _, coef) -> l
  | Close (l, _, _, _, _, _, coef) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _, _) -> l
  | Throw (l, _) -> l
  | TryCatch (l, _, _) -> l
  | TryFinally (l, _, _, _) -> l
  | BlockStmt (l, ds, ss, _, _) -> l
  | PerformActionStmt (l, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> l
  | SplitFractionStmt (l, _, _, _, _) -> l
  | MergeFractionsStmt (l, _, _, _) -> l
  | CreateBoxStmt (l, _, _, _, _) -> l
  | CreateHandleStmt (l, _, _, _) -> l
  | DisposeBoxStmt (l, _, _, _) -> l
  | LabelStmt (l, _) -> l
  | GotoStmt (l, _) -> l
  | NoopStmt l -> l
  | InvariantStmt (l, _) -> l
  | ProduceLemmaFunctionPointerChunkStmt (l, _, _, _) -> l
  | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) -> l
  | Break (l) -> l
  | SuperConstructorCall(l, _) -> l

let type_expr_loc t =
  match t with
    ManifestTypeExpr (l, t) -> l
  | StructTypeExpr (l, sn) -> l
  | IdentTypeExpr (l, _, x) -> l
  | ConstructedTypeExpr (l, x, targs) -> l
  | PtrTypeExpr (l, te) -> l
  | ArrayTypeExpr(l, te) -> l
  | PredTypeExpr(l, te, _) -> l
  | PureFuncTypeExpr (l, tes) -> l

let expr_fold_open iter state e =
  let rec iters state es =
    match es with
      [] -> state
    | e::es -> iters (iter state e) es
  and iterpats state pats =
    match pats with
      [] -> state
    | LitPat e::pats -> iterpats (iter state e) pats
    | _::pats -> iterpats state pats
  and itercs state cs =
    match cs with
      [] -> state
    | SwitchExprClause (l, cn, pats, e)::cs -> itercs (iter state e) cs
  in
  match e with
    True l -> state
  | False l -> state
  | Null l -> state
  | Var (l, x, scope) -> state
  | Operation (l, op, es, ts) -> iters state es
  | IntLit (l, n, tp) -> state
  | RealLit(l, n) -> state
  | StringLit (l, s) -> state
  | ClassLit (l, cn) -> state
  | Read (l, e0, f) -> iter state e0
  | ArrayLengthExpr (l, e0) -> iter state e0
  | WRead (l, e0, fparent, fname, frange, fstatic, fvalue, fghost) -> if fstatic then state else iter state e0
  | ReadArray (l, a, i) -> let state = iter state a in let state = iter state i in state
  | WReadArray (l, a, tp, i) -> let state = iter state a in let state = iter state i in state
  | Deref (l, e0, tp) -> iter state e0
  | CallExpr (l, g, targes, pats0, pats, mb) -> let state = iterpats state pats0 in let state = iterpats state pats in state
  | ExprCallExpr (l, e, es) -> iters state (e::es)
  | WPureFunCall (l, g, targs, args) -> iters state args
  | WPureFunValueCall (l, e, args) -> iters state (e::args)
  | WFunCall (l, g, targs, args) -> iters state args
  | WFunPtrCall (l, g, args) -> iters state args
  | WMethodCall (l, cn, m, pts, args, mb) -> iters state args
  | NewObject (l, cn, args) -> iters state args
  | NewArray (l, te, e0) -> iter state e0
  | NewArrayWithInitializer (l, te, es) -> iters state es
  | IfExpr (l, e1, e2, e3) -> iters state [e1; e2; e3]
  | SwitchExpr (l, e0, cs, cdef_opt, info) -> let state = itercs (iter state e0) cs in (match cdef_opt with Some (l, e) -> iter state e | None -> state)
  | PredNameExpr (l, p) -> state
  | CastExpr (l, trunc, te, e0) -> iter state e0
  | Upcast (e, fromType, toType) -> iter state e
  | WidenedParameterArgument e -> iter state e
  | SizeofExpr (l, te) -> state
  | AddressOf (l, e0) -> iter state e0
  | ProverTypeConversion (pt, pt0, e0) -> iter state e0
  | AssignExpr (l, lhs, rhs) -> iter (iter state lhs) rhs
  | AssignOpExpr (l, lhs, op, rhs, post, _, _) -> iter (iter state lhs) rhs
  | InstanceOfExpr(l, e, tp) -> iter state e
  | SuperMethodCall(_, _, args) -> iters state args
  | WSuperMethodCall(_, _, args, _) -> iters state args

(* Postfix fold *)
let expr_fold f state e = let rec iter state e = f (expr_fold_open iter state e) e in iter state e

let expr_iter f e = expr_fold (fun state e -> f e) () e

let expr_flatmap f e = expr_fold (fun state e -> f e @ state) [] e

(* Region: the parser *)

let common_keywords = [
  "switch"; "case"; ":"; "return"; "for";
  "void"; "if"; "else"; "while"; "!="; "<"; ">"; "<="; ">="; "&&"; "++"; "--"; "+="; "-="; "*="; "/="; "&="; "|="; "^="; "%="; "<<="; ">>="; ">>>=";
  "||"; "!"; "["; "]"; "{"; "break"; "default";
  "}"; ";"; "int"; "true"; "false"; "("; ")"; ","; "="; "|"; "+"; "-"; "=="; "?"; "%"; 
  "*"; "/"; "&"; "^"; "~"; "assert"; "currentCodeFraction"; "currentThread"; "short"; ">>"; "<<";
  "truncating"; "typedef"; "do"
]

let ghost_keywords = [
  "predicate"; "requires"; "|->"; "&*&"; "inductive"; "fixpoint";
  "ensures"; "close"; "lemma"; "open"; "emp"; "invariant"; "lemma_auto";
  "_"; "@*/"; "predicate_family"; "predicate_family_instance"; "predicate_ctor"; "leak"; "@";
  "box_class"; "action"; "handle_predicate"; "preserved_by"; "consuming_box_predicate"; "consuming_handle_predicate"; "perform_action"; "nonghost_callers_only";
  "create_box"; "and_handle"; "create_handle"; "dispose_box"; "produce_lemma_function_pointer_chunk"; "produce_function_pointer_chunk";
  "producing_box_predicate"; "producing_handle_predicate"; "box"; "handle"; "any"; "real"; "split_fraction"; "by"; "merge_fractions";
  "unloadable_module"; "decreases"; "load_plugin"
]

let c_keywords = [
  "struct"; "bool"; "char"; "->"; "sizeof"; "#"; "include"; "ifndef";
  "define"; "endif"; "&"; "goto"; "uintptr_t"; "INT_MIN"; "INT_MAX";
  "UINTPTR_MAX"; "enum"; "static"; "signed"; "unsigned"; "long";
  "volatile"; "register"; "ifdef"; "elif"; "undef"
]

let java_keywords = [
  "public"; "char"; "private"; "protected"; "class"; "."; "static"; "boolean"; "new"; "null"; "interface"; "implements"; "package"; "import";
  "throw"; "try"; "catch"; "throws"; "byte"; "final"; "extends"; "instanceof"; "super"; "abstract"
]

exception StaticError of loc * string * string option

let static_error l msg url = raise (StaticError (l, msg, url))

exception CompilationError of string

let file_type path=
  begin
  if Filename.check_suffix (Filename.basename path) ".c" then CLang
  else if Filename.check_suffix (Filename.basename path) ".jarsrc" then Java
  else if Filename.check_suffix (Filename.basename path) ".jarspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".java" then Java
  else if Filename.check_suffix (Filename.basename path) ".javaspec" then Java
  else if Filename.check_suffix (Filename.basename path) ".scala" then Java
  else if Filename.check_suffix (Filename.basename path) ".h" then CLang
  else raise (CompilationError ("unknown extension: " ^ (Filename.basename path)))
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

type spec_clause = (* ?spec_clause *)
  NonghostCallersOnlyClause
| FuncTypeClause of string * type_expr list * (loc * string) list
| RequiresClause of asn
| EnsuresClause of asn

(* A toy Scala parser. *)
module Scala = struct

  let keywords = [
    "def"; "var"; "class"; "object"; "."; "new"; "null"; "package"; "import";
    "+"; "="; "("; ")"; ":"; "{"; "}"; "["; "]"; "/*@"; "@*/"; "=="; "="; ";"; "true"; "false"; "assert"
  ]

  let rec
    parse_decl = parser
      [< '(l, Kwd "object"); '(_, Ident cn); '(_, Kwd "{"); ms = rep parse_method; '(_, Kwd "}") >] ->
      Class (l, false, FinalClass, cn, ms, [], [], "Object", [], [])
  and
    parse_method = parser
      [< '(l, Kwd "def"); '(_, Ident mn); ps = parse_paramlist; t = parse_type_ann; co = parse_contract; '(_, Kwd "=");'(_, Kwd "{"); ss = rep parse_stmt; '(closeBraceLoc, Kwd "}")>] ->
      let rt = match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t in
      Meth (l, Real, rt, mn, ps, Some co,Some (ss, closeBraceLoc), Static, Public, false)
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
        | (_, []) -> IdentTypeExpr (l, None, tn)
        | _ -> raise (ParseException (l, "Type arguments are not supported."))
      end
  and
    parse_targlist = parser
      [< '(_, Kwd "["); ts = rep_comma parse_type; '(_, Kwd "]") >] -> ts
    | [< >] -> []
  and
    parse_contract = parser
      [< '(_, Kwd "/*@"); '(_, Kwd "requires"); pre = parse_asn; '(_, Kwd "@*/");
         '(_, Kwd "/*@"); '(_, Kwd "ensures"); post = parse_asn; '(_, Kwd "@*/") >] -> (pre, post, [])
  and
    parse_asn = parser
      [< '(_, Kwd "("); a = parse_asn; '(_, Kwd ")") >] -> a
    | [< e = parse_expr >] -> ExprAsn (expr_loc e, e)
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
      [< '(l, Kwd "var"); '(_, Ident x); t = parse_type_ann; '(_, Kwd "="); e = parse_expr; '(_, Kwd ";") >] -> DeclStmt (l, [l, t, x, Some(e), ref false])
    | [< '(l, Kwd "assert"); a = parse_asn; '(_, Kwd ";") >] -> Assert (l, a)

end

(* The C/Java parser.
   The difference is in the scanner: when parsing a C file, the scanner treats "class" like an identifier, not a keyword.
   And Kwd "class" does not match Ident "class".
   *)

type modifier = StaticModifier | FinalModifier | AbstractModifier | VisibilityModifier of visibility

let parse_decls =
let rec
  parse_decls = parser
  [< '((p1, _), Kwd "/*@"); ds = parse_pure_decls; '((_, p2), Kwd "@*/"); ds' = parse_decls >] -> ds @ ds'
| [< _ = opt (parser [< '(_, Kwd "public") >] -> ());
     abstract = (parser [< '(_, Kwd "abstract") >] -> true | [< >] -> false); 
     final = (parser [< '(_, Kwd "final") >] -> FinalClass | [< >] -> ExtensibleClass);
     ds = begin parser
       [< '(l, Kwd "class"); '(_, Ident s); super = parse_super_class; il = parse_interfaces; mem = parse_java_members s; ds = parse_decls >]
       -> Class (l, abstract, final, s, methods s mem, fields mem, constr mem, super, il, instance_preds mem)::ds
     | [< '(l, Kwd "interface"); '(_, Ident cn); il = parse_extended_interfaces;  mem = parse_java_members cn; ds = parse_decls >]
       -> Interface (l, cn, il, fields mem, methods cn mem, instance_preds mem)::ds
     | [< d = parse_decl; ds = parse_decls >] -> d@ds
     | [< >] -> []
     end
  >] -> ds
and parse_qualified_type_rest = parser
  [< '(_, Kwd "."); '(_, Ident s); rest = parse_qualified_type_rest >] -> "." ^ s ^ rest
| [<>] -> ""
and parse_qualified_type = parser
  [<'(_, Ident s); rest = parse_qualified_type_rest >] -> s ^ rest
and
  parse_super_class= parser
    [<'(_, Kwd "extends"); s = parse_qualified_type >] -> s 
  | [<>] -> "java.lang.Object"
and
  parse_interfaces= parser
  [< '(_, Kwd "implements"); is = rep_comma (parser 
    [< i = parse_qualified_type; e=parser
      [<>]->(i)>] -> e); '(_, Kwd "{") >] -> is
| [<'(_, Kwd "{")>]-> []
and
  parse_extended_interfaces= parser
  [< '(_, Kwd "extends"); is = rep_comma (parser 
    [< i = parse_qualified_type; e=parser
      [<>]->(i)>] -> e); '(_, Kwd "{") >] -> is
| [<'(_, Kwd "{")>]-> []
and
  methods cn m=
  match m with
    MethMember (Meth (l, gh, t, n, ps, co, ss,s,v,abstract))::ms -> Meth (l, gh, t, n, ps, co, ss,s,v,abstract)::(methods cn ms)
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
  parse_interface_visibility = parser
  [<'(_, Kwd "public")>] -> Public
| [<>] -> Public
and
  parse_visibility = parser
  [<'(_, Kwd "public")>] -> Public
| [<'(_, Kwd "private")>] -> Private
| [<'(_, Kwd "protected")>] -> Protected
| [<>] -> Package
and
  parse_java_members cn= parser
  [<'(_, Kwd "}")>] -> []
| [< '(_, Kwd "/*@"); mems1 = parse_ghost_java_members cn; mems2 = parse_java_members cn >] -> mems1 @ mems2
| [< m=parse_java_member cn;mr=parse_java_members cn>] -> m::mr
and
  parse_ghost_java_members cn = parser
  [< '(_, Kwd "@*/") >] -> []
| [< vis = parse_visibility; m = begin parser
       [< '(l, Kwd "predicate"); '(_, Ident g); ps = parse_paramlist;
          body = begin parser
            [< '(_, Kwd "="); p = parse_pred >] -> Some p
          | [< >] -> None
          end;
          '(_, Kwd ";") >] -> PredMember (InstancePredDecl (l, g, ps, body))
     | [< '(l, Kwd "lemma"); t = parse_return_type; '(l, Ident x); (ps, co, ss) = parse_method_rest >] ->
       let ps = (IdentTypeExpr (l, None, cn), "this")::ps in
       MethMember (Meth (l, Ghost, t, x, ps, co, ss, Instance, vis, false))
     | [< binding = (parser [< '(_, Kwd "static") >] -> Static | [< >] -> Instance); t = parse_type; '(l, Ident x); '(_, Kwd ";") >] ->
       FieldMember [Field (l, Ghost, t, x, binding, vis, false, None)]
     end;
     mems = parse_ghost_java_members cn
  >] -> m::mems
and
  parse_qualified_identifier = parser
  [< '(l, Ident x); xs = rep (parser [< '(_, Kwd "."); '(l, Ident x) >] -> (l, x)) >] -> (l, x)::xs
and
  parse_thrown = parser
  [< tp = parse_type; '(_, Kwd "/*@"); '(_, Kwd "ensures"); epost = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> (tp, epost)
and
  parse_throws_clause = parser
  [< '(l, Kwd "throws"); epost = rep_comma parse_thrown >] -> epost
and
  parse_array_dims t = parser
  [< '(l, Kwd "["); '(_, Kwd "]"); t = parse_array_dims (ArrayTypeExpr (l, t)) >] -> t
| [< >] -> t
and 
  id x = parser [< >] -> x
and 
  parse_java_modifier = parser [< '(_, Kwd "public") >] -> VisibilityModifier(Public) | [< '(_, Kwd "protected") >] -> VisibilityModifier(Protected) | [< '(_, Kwd "private") >] -> VisibilityModifier(Private) | [< '(_, Kwd "static") >] -> StaticModifier | [< '(_, Kwd "final") >] -> FinalModifier | [< '(_, Kwd "abstract") >] -> AbstractModifier
and
  parse_java_member cn = parser
  [< modifiers = rep parse_java_modifier;
     binding = (fun _ -> if List.mem StaticModifier modifiers then Static else Instance);
     final = (fun _ -> List.mem FinalModifier modifiers);
     abstract = (fun _ -> List.mem AbstractModifier modifiers);
     vis = (fun _ -> (match (try_find (function VisibilityModifier(_) -> true | _ -> false) modifiers) with None -> Package | Some(VisibilityModifier(vis)) -> vis));
     t = parse_return_type;
     member = parser
       [< '(l, Ident x);
          member = parser
            [< (ps, co, ss) = parse_method_rest >] ->
            let ps = if binding = Instance then (IdentTypeExpr (l, None, cn), "this")::ps else ps in
            MethMember (Meth (l, Real, t, x, ps, co, ss, binding, vis, abstract))
          | [< t = id (match t with None -> raise (ParseException (l, "A field cannot be void.")) | Some(t) -> t);
               tx = parse_array_braces t;
               init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
               ds = comma_rep (parse_declarator t); '(_, Kwd ";")
            >] ->
            let fds =
              ((l, tx, x, init, ref false)::ds) |> List.map begin fun (l, tx, x, init, _) ->
                Field (l, Real, tx, x, binding, vis, final, init)
              end
            in
            FieldMember fds
       >] -> member
     | [< (ps, co, ss) = parse_method_rest >] ->
       let l =
         match t with
           None -> raise (Stream.Error "Keyword 'void' cannot be followed by a parameter list.")
         | Some (IdentTypeExpr (l, None, x)) -> if x = cn then l else raise (ParseException (l, "Constructor name does not match class name."))
         | Some t -> raise (ParseException (type_expr_loc t, "Constructor name expected."))
       in
       if binding = Static then raise (ParseException (l, "A constructor cannot be static."));
       if final then raise (ParseException (l, "A constructor cannot be final."));
       ConsMember (Cons (l, ps, co, ss, vis))
  >] -> member
and parse_array_init_rest = parser
  [< '(_, Kwd ","); es = opt(parser [< e = parse_expr; es = parse_array_init_rest >] -> e :: es) >] -> (match es with None -> [] | Some(es) -> es)
| [< >] -> []
and parse_array_init = parser
  [< '(_, Kwd ","); '(_, Kwd "}") >] -> []
| [< '(_, Kwd "}") >] -> []
| [< e = parse_expr; es = parse_array_init_rest; '(_, Kwd "}") >] -> e :: es
and parse_declaration_rhs te = parser
  [< '(linit, Kwd "{"); es = parse_array_init >] ->
  (match te with ArrayTypeExpr (_, elem_te) -> NewArrayWithInitializer (linit, elem_te, es) | _ -> InitializerList (linit, es))
| [< e = parse_expr >] -> e
and
  parse_declarator t = parser
  [< '(l, Ident x);
     tx = parse_array_braces t;
     init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
  >] -> (l, tx, x, init, ref false)
and
  parse_method_rest = parser
  [< ps = parse_paramlist;
    epost = opt parse_throws_clause;
    (ss, co) = parser
      [< '(_, Kwd ";"); spec = opt parse_spec >] -> (None, spec)
    | [< spec = opt parse_spec; ss = parse_some_block >] -> (ss, spec)
    >] -> (ps, (match co with None -> None | Some(pre, post) -> Some (pre, post, (match epost with None -> [] | Some(epost) -> epost))), ss)
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
| [< '(l, Kwd "typedef"); rt = parse_return_type; '(_, Ident g);
     ds = begin parser
       [< (ftps, ps) = parse_functype_paramlists; '(_, Kwd ";"); (pre, post) = parse_spec >] -> [FuncTypeDecl (l, Real, rt, g, [], ftps, ps, (pre, post))]
     | [< '(_, Kwd ";") >] -> begin match rt with None -> raise (ParseException (l, "Void not allowed here.")) | Some te -> [TypedefDecl (l, te, g)] end
     end
  >] -> ds
| [< '(_, Kwd "enum"); '(l, Ident n); '(_, Kwd "{");
     elems = rep_comma (parser [< '(_, Ident e); init = opt (parser [< '(_, Kwd "="); e = parse_expr >] -> e) >] -> (e, init));
     '(_, Kwd "}"); '(_, Kwd ";"); >] ->
  [EnumDecl(l, n, elems)]
| [< '(_, Kwd "static"); t = parse_return_type; d = parse_func_rest Regular t >] -> [d]
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
  parse_pred_paramlist = parser
    [< 
      '(_, Kwd "("); ps = rep_comma parse_param;
      (ps, inputParamCount) = (parser [< '(_, Kwd ";"); ps' = rep_comma parse_param >] -> (ps @ ps', Some (List.length ps)) | [< >] -> (ps, None)); '(_, Kwd ")")
    >] -> (ps, inputParamCount)
and
  parse_pure_decl = parser
    [< '(l, Kwd "inductive"); '(li, Ident i); tparams = parse_type_params li; '(_, Kwd "="); cs = (parser [< cs = parse_ctors >] -> cs | [< cs = parse_ctors_suffix >] -> cs); '(_, Kwd ";") >] -> [Inductive (l, i, tparams, cs)]
  | [< '(l, Kwd "fixpoint"); t = parse_return_type; d = parse_func_rest Fixpoint t >] -> [d]
  | [< '(l, Kwd "predicate"); '(li, Ident g); tparams = parse_type_params li; 
     (ps, inputParamCount) = parse_pred_paramlist;
     body = opt parse_pred_body;
     '(_, Kwd ";");
    >] ->
    [PredFamilyDecl (l, g, tparams, 0, List.map (fun (t, p) -> t) ps, inputParamCount)] @
    (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
  | [< '(l, Kwd "predicate_family"); '(_, Ident g); is = parse_paramlist; (ps, inputParamCount) = parse_pred_paramlist; '(_, Kwd ";") >]
  -> [PredFamilyDecl (l, g, [], List.length is, List.map (fun (t, p) -> t) ps, inputParamCount)]
  | [< '(l, Kwd "predicate_family_instance"); '(_, Ident g); is = parse_index_list; ps = parse_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredFamilyInstanceDecl (l, g, [], is, ps, p)]
  | [< '(l, Kwd "predicate_ctor"); '(_, Ident g); ps1 = parse_paramlist; ps2 = parse_paramlist;
     p = parse_pred_body; '(_, Kwd ";"); >] -> [PredCtorDecl (l, g, ps1, ps2, p)]
  | [< '(l, Kwd "lemma"); t = parse_return_type; d = parse_func_rest (Lemma(false, None)) t >] -> [d]
  | [< '(l, Kwd "lemma_auto"); trigger = opt (parser [< '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); >] -> e); t = parse_return_type; d = parse_func_rest (Lemma(true, trigger)) t >] -> [d]
  | [< '(l, Kwd "box_class"); '(_, Ident bcn); ps = parse_paramlist;
       '(_, Kwd "{"); '(_, Kwd "invariant"); inv = parse_pred; '(_, Kwd ";");
       ads = parse_action_decls; hpds = parse_handle_pred_decls; '(_, Kwd "}") >] -> [BoxClassDecl (l, bcn, ps, inv, ads, hpds)]
  | [< '(l, Kwd "typedef"); '(_, Kwd "lemma"); rt = parse_return_type; '(li, Ident g); tps = parse_type_params li;
       (ftps, ps) = parse_functype_paramlists; '(_, Kwd ";"); (pre, post) = parse_spec >] ->
    [FuncTypeDecl (l, Ghost, rt, g, tps, ftps, ps, (pre, post))]
  | [< '(l, Kwd "unloadable_module"); '(_, Kwd ";") >] -> [UnloadableModuleDecl l]
  | [< '(l, Kwd "load_plugin"); '(lx, Ident x); '(_, Kwd ";") >] -> [LoadPluginDecl (l, lx, x)]
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
  parse_type_params_free = parser [< '(_, Kwd "<"); xs = rep_comma (parser [< '(_, Ident x) >] -> x); '(_, Kwd ">") >] -> xs
and
  parse_type_params_general = parser
  [< xs = parse_type_params_free >] -> xs
| [< xs = peek_in_ghost_range (parser [< xs = parse_type_params_free; '(_, Kwd "@*/") >] -> xs) >] -> xs
| [< >] -> []
and
  parse_func_rest k t = parser
  [<
    '(l, Ident g);
    tparams = parse_type_params_general;
    decl = parser
      [<
        ps = parse_paramlist;
        f = parser
          [< '(_, Kwd ";"); (nonghost_callers_only, ft, co) = parse_spec_clauses >] ->
          Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, None, Static, Public)
        | [< (nonghost_callers_only, ft, co) = parse_spec_clauses; '(_, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
          Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, Some (ss, closeBraceLoc), Static, Public)
      >] -> f
    | [<
        () = (fun s -> if k = Regular && tparams = [] && t <> None then () else raise Stream.Failure);
        t = parse_array_braces (get t);
        init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs t >] -> e);
        '(_, Kwd ";")
      >] -> Global (l, t, g, init)
  >] -> decl
and
  parse_ctors_suffix = parser
  [< '(_, Kwd "|"); cs = parse_ctors >] -> cs
| [< >] -> []
and parse_ctors = parser
  [< '(l, Ident cn); ts = (parser [< '(_, Kwd "("); ts = rep_comma parse_paramtype; '(_, Kwd ")") >] -> ts | [< >] -> []); cs = parse_ctors_suffix >] -> Ctor (l, cn, ts)::cs
and
  parse_paramtype = parser [< t = parse_type; _ = opt (parser [< '(_, Ident _) >] -> ()) >] -> t
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
  [< te0 = parse_type; '(l, Ident f);
     te = parser
        [< '(_, Kwd ";") >] -> te0
      | [< '(_, Kwd "["); '(ls, Int size); '(_, Kwd "]"); '(_, Kwd ";") >] ->
          (match te0 with (ManifestTypeExpr (_, _) | PtrTypeExpr (_, _)) ->
            if ( (int_of_big_int size) <= 0 ) then
              raise (ParseException (ls, "Array must have size > 0."));
            StaticArrayTypeExpr (l, te0, (int_of_big_int size))
          | _ -> raise (ParseException (l, "Array cannot be of this type.")))
   >] -> Field (l, gh, te, f, Instance, Public, false, None)
and
  parse_return_type = parser
  [< t = parse_type >] -> match t with ManifestTypeExpr (_, Void) -> None | _ -> Some t
and
  parse_type = parser
  [< t0 = parse_primary_type; t = parse_type_suffix t0 >] -> t
and
  parse_primary_type = parser
  [< '(l, Kwd "volatile"); t0 = parse_primary_type >] -> t0
| [< '(l, Kwd "register"); t0 = parse_primary_type >] -> t0
| [< '(l, Kwd "struct"); '(_, Ident s) >] -> StructTypeExpr (l, s)
| [< '(l, Kwd "enum"); '(_, Ident _) >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "int") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "short") >] -> ManifestTypeExpr(l, ShortType)
| [< '(l, Kwd "long") >] -> ManifestTypeExpr (l, IntType)
| [< '(l, Kwd "signed"); t0 = parse_primary_type >] ->
  (match t0 with
     (ManifestTypeExpr (_, IntType) | ManifestTypeExpr (_, ShortType) |
      ManifestTypeExpr (_, Char)) -> t0
   | _ -> raise (ParseException (l, "This type cannot be signed.")))
| [< '(l, Kwd "unsigned"); t0 = parse_primary_type >] ->
  (match t0 with
     ManifestTypeExpr (l, IntType) -> ManifestTypeExpr (l, UintPtrType)
   | ManifestTypeExpr (l, ShortType) -> ManifestTypeExpr (l, UShortType)
   | ManifestTypeExpr (l, Char) -> ManifestTypeExpr (l, UChar)
   | _ -> raise (ParseException (l, "This type cannot be unsigned.")))
| [< '(l, Kwd "uintptr_t") >] -> ManifestTypeExpr (l, UintPtrType)
| [< '(l, Kwd "real") >] -> ManifestTypeExpr (l, RealType)
| [< '(l, Kwd "bool") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "boolean") >] -> ManifestTypeExpr (l, Bool)
| [< '(l, Kwd "void") >] -> ManifestTypeExpr (l, Void)
| [< '(l, Kwd "char") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "byte") >] -> ManifestTypeExpr (l, Char)
| [< '(l, Kwd "predicate");
     '(_, Kwd "(");
     ts = rep_comma parse_paramtype;
     ts' = opt (parser [< '(_, Kwd ";"); ts' = rep_comma parse_paramtype >] -> ts');
     '(_, Kwd ")")
  >] -> begin match ts' with None -> PredTypeExpr (l, ts, None) | Some ts' -> PredTypeExpr (l, ts @ ts', Some (List.length ts)) end
| [< '(l, Kwd "fixpoint"); '(_, Kwd "("); ts = rep_comma parse_paramtype; '(_, Kwd ")") >] -> PureFuncTypeExpr (l, ts)
| [< '(l, Kwd "box") >] -> ManifestTypeExpr (l, BoxIdType)
| [< '(l, Kwd "handle") >] -> ManifestTypeExpr (l, HandleIdType)
| [< '(l, Kwd "any") >] -> ManifestTypeExpr (l, AnyType)
| [< '(l, Ident n); rest = rep(parser [< '(l, Kwd "."); '(l, Ident n) >] -> n); targs = parse_type_args l;  >] -> 
    if targs <> [] then 
      match rest with
      | [] ->  ConstructedTypeExpr (l, n, targs) 
      | _ -> raise (ParseException (l, "Package name not supported for generic types."))
    else
      match rest with
        [] -> IdentTypeExpr(l, None, n)
      | _ -> 
      let pac = (String.concat "." (n :: (take ((List.length rest) -1) rest))) in
      IdentTypeExpr(l, Some (pac), List.nth rest ((List.length rest) - 1))
and 
  parse_type_suffix t0 = parser
  [< '(l, Kwd "*"); t = parse_type_suffix (PtrTypeExpr (l, t0)) >] -> t
| [< '(l, Kwd "["); '(_, Kwd "]");>] -> ArrayTypeExpr(l,t0)
| [< >] -> t0
and
(* parse function parameters: *)
  parse_paramlist =
  parser
    [< '(_, Kwd "("); ps = rep_comma parse_param; '(_, Kwd ")") >] ->
    List.filter filter_void_params ps
and
  filter_void_params ps = match ps with
    (ManifestTypeExpr (_, Void), "") -> false
  | _ -> true
and
  parse_param = parser [< t = parse_type; pn = parse_param_name; is_array = opt(parser [< '(l, Kwd "[");'(_, Kwd "]") >] -> l) >] ->
    begin match t with
      ManifestTypeExpr (_, Void) -> 
      begin match pn with
        None -> (t, "")
      | Some((l, pname)) -> raise (ParseException (l, "A parameter cannot be of type void."))
      end
    | _ -> 
      begin match pn with
        None -> raise (ParseException (type_expr_loc t, "Illegal parameter."));
      | Some((l, pname)) -> 
        begin match is_array with
          None -> (t, pname)
        | Some(_) -> (ArrayTypeExpr(type_expr_loc t, t), pname)
        end
      end
    end
and
  parse_param_name = parser
    [< '(l, Ident pn) >] -> Some (l, pn)
  | [< >] -> None
and
  parse_functypeclause_args = parser
  [< '(_, Kwd "("); args = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")") >] -> args
| [< >] -> []
and
  parse_pure_spec_clause = parser
  [< '(_, Kwd "nonghost_callers_only") >] -> NonghostCallersOnlyClause
| [< '(_, Kwd ":"); '(li, Ident ft); targs = parse_type_args li; ftargs = parse_functypeclause_args >] -> FuncTypeClause (ft, targs, ftargs)
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
    let nonghost_callers_only = (parser [< 'NonghostCallersOnlyClause >] -> out_count := !out_count + 1; true | [< >] -> false) clause_stream in
    let ft = (parser [< 'FuncTypeClause (ft, fttargs, ftargs) >] -> out_count := !out_count + 1; Some (ft, fttargs, ftargs) | [< >] -> None) clause_stream in
    let pre_post = (parser [< 'RequiresClause pre; 'EnsuresClause post; >] -> out_count := !out_count + 2; Some (pre, post) | [< >] -> None) clause_stream in
    if !in_count > !out_count then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: nonghost_callers_only clause (optional), function type clause (optional), contract (optional).");
    (nonghost_callers_only, ft, pre_post)
and
  parse_spec = parser
    [< (nonghost_callers_only, ft, pre_post) = parse_spec_clauses >] ->
    match (nonghost_callers_only, ft, pre_post) with
      (false, None, None) -> raise Stream.Failure
    | (false, None, (Some (pre, post))) -> (pre, post)
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
     (l, ds, ss, locals_to_free) = (parser
       [< '((sp1, _), Kwd "/*@");
          b = parser
          | [< d = parse_pure_decl; ds = parse_pure_decls; '(_, Kwd "@*/"); ss = parse_stmts >] -> (l, d @ ds, ss, ref [])
          | [< s = parse_stmt0; '((_, sp2), Kwd "@*/"); ss = parse_stmts >] -> (l, [], PureStmt ((sp1, sp2), s)::ss, ref [])
       >] -> b
     | [< ds = parse_pure_decls; ss = parse_stmts >] -> (l, ds, ss, ref []));
     '(closeBraceLoc, Kwd "}")
  >] -> BlockStmt(l, ds, ss, closeBraceLoc, locals_to_free)
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
     CallExpr (_, g, targs, es1, es2, Static) ->
       stats#openParsed;
       Open (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       stats#openParsed;
       Open (l, Some target, g, targs, es1, es2, coef)
   | _ -> raise (ParseException (l, "Body of open statement must be call expression.")))
| [< '(l, Kwd "close"); coef = opt parse_coef; e = parse_expr; '(_, Kwd ";") >] ->
  (match e with
     CallExpr (_, g, targs, es1, es2, Static) ->
       stats#closeParsed;
       Close (l, None, g, targs, es1, es2, coef)
   | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
       stats#closeParsed;
       Close (l, Some target, g, targs, es1, es2, coef)
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
| [< '(l, Kwd "produce_lemma_function_pointer_chunk"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")");
     ftclause = begin parser
       [< '(_, Kwd ":");
          '(li, Ident ftn);
          targs = parse_type_args li;
          args = parse_arglist;
          '(_, Kwd "("); params = rep_comma (parser [< '(l, Ident x) >] -> (l, x)); '(_, Kwd ")");
          '(openBraceLoc, Kwd "{"); ss = parse_stmts; '(closeBraceLoc, Kwd "}") >] ->
       Some (ftn, targs, args, params, openBraceLoc, ss, closeBraceLoc)
     | [< >] -> None
     end;
     body = parser
       [< '(_, Kwd ";") >] -> None
     | [< s = parse_stmt >] -> Some s
  >] -> ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause, body)
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
     (inv, dec, body) = parse_loop_core
  >] -> WhileStmt (l, e, inv, dec, body)
| [< '(l, Kwd "do"); (inv, dec, body) = parse_loop_core; '(lwhile, Kwd "while"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] ->
  (* "do S while (E);" is translated to "while (true) { S if (E) {} else break; }" *)
  (* CAVEAT: If we ever add support for 'continue' statements, then this translation is not sound. *)
  WhileStmt (l, True l, inv, dec, body @ [IfStmt (lwhile, e, [], [Break lwhile])])
| [< '(l, Kwd "for");
     '(_, Kwd "(");
     init_stmts = begin parser
       [< e = parse_expr;
          ss = parser
            [< '(l, Ident x); s = parse_decl_stmt_rest (type_expr_of_expr e) l x >] -> [s]
          | [< es = comma_rep parse_expr; '(_, Kwd ";") >] -> List.map (fun e -> ExprStmt e) (e::es)
       >] -> ss
     | [< te = parse_type; '(l, Ident x); s = parse_decl_stmt_rest te l x >] -> [s]
     | [< '(_, Kwd ";") >] -> []
     end;
     cond = opt parse_expr;
     '(_, Kwd ";");
     update_exprs = rep_comma parse_expr;
     '(_, Kwd ")");
     (inv, dec, b) = parse_loop_core
  >] ->
  let cond = match cond with None -> True l | Some e -> e in
  BlockStmt (l, [], init_stmts @ [WhileStmt (l, cond, inv, dec, b @ List.map (fun e -> ExprStmt e) update_exprs)], l, ref [])
| [< '(l, Kwd "throw"); e = parse_expr; '(_, Kwd ";") >] -> Throw (l, e)
| [< '(l, Kwd "break"); '(_, Kwd ";") >] -> Break(l)
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
     '(lpa, Kwd "perform_action"); '(_, Ident an); aargs = parse_arglist;
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
     PerformActionStmt (lcb, ref false, pre_bpn, pre_bp_args, lch, pre_hpn, pre_hp_args, lpa, an, aargs, ss, closeBraceLoc, post_bp_args, lph, post_hpn, post_hp_args)
| [< '(l, Kwd ";") >] -> NoopStmt l
| [< '(l, Kwd "super"); s = parser 
     [< '(_, Kwd "."); '(l2, Ident n); '(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")") >] -> ExprStmt(SuperMethodCall (l, n, es))
   | [<'(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] -> SuperConstructorCall (l, es)
  >] -> s
| [< e = parse_expr; s = parser
    [< '(_, Kwd ";") >] ->
    begin match e with
      AssignExpr (l, Operation (llhs, Mul, [Var (lt, t, _); Var (lx, x, _)], _), rhs) -> DeclStmt (l, [l, PtrTypeExpr (llhs, IdentTypeExpr (lt, None, t)), x, Some(rhs), ref false])
    | _ -> ExprStmt e
    end
  | [< '(l, Kwd ":") >] -> (match e with Var (_, lbl, _) -> LabelStmt (l, lbl) | _ -> raise (ParseException (l, "Label must be identifier.")))
  | [< '(lx, Ident x); s = parse_decl_stmt_rest (type_expr_of_expr e) lx x >] -> s
  >] -> s
(* parse variable declarations: *)
| [< te = parse_type; '(lx, Ident x); s2 = parse_decl_stmt_rest te lx x >] ->
  ( try match te with
     ManifestTypeExpr (l, Void) ->
      raise (ParseException (l, "A variable cannot be of type void."))
    with
     Match_failure _ -> s2 )
and
  parse_loop_core = parser [<
    inv =
      opt
        begin parser
          [< '(_, Kwd "/*@");
             inv = begin parser
               [< '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> LoopInv p
             | [< '(_, Kwd "requires"); pre = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/");
                  '(_, Kwd "/*@"); '(_, Kwd "ensures"); post = parse_pred; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> LoopSpec (pre, post)
             end
          >] -> inv
        | [< '(_, Kwd "invariant"); p = parse_pred; '(_, Kwd ";"); >] -> LoopInv p
        end;
    dec = opt (parser [< '(_, Kwd "/*@"); '(_, Kwd "decreases"); decr = parse_expr; '(_, Kwd ";"); '(_, Kwd "@*/") >] -> decr | [< '(_, Kwd "decreases"); decr = parse_expr; '(_, Kwd ";"); >] -> decr );(* only allows decreases if invariant provided *)
    body = parse_stmt;
  >] -> (inv, dec, [body])
and
  packagename_of_read l e =
  match e with
  | Var(_, x, _) when x <> "this" -> x
  | Read(_, e, f) -> (packagename_of_read l e) ^ "." ^ f
  | e -> raise (ParseException (l, "Type expected."))
and
  type_expr_of_expr e =
  match e with
    Var (l, x, _) -> IdentTypeExpr (l, None, x)
  | CallExpr (l, x, targs, [], [], Static) -> ConstructedTypeExpr (l, x, targs)
  | ArrayTypeExpr' (l, e) -> ArrayTypeExpr (l, type_expr_of_expr e)
  | Read(l, e, name) -> IdentTypeExpr(l, Some(packagename_of_read l e), name)
  | e -> raise (ParseException (expr_loc e, "Type expected."))
and parse_array_braces te = parser
  [< '(l, Kwd "[");
     te = begin parser
       [< '(lsize, Int size) >] ->
       if sign_big_int size <= 0 then raise (ParseException (lsize, "Array must have size > 0."));
       StaticArrayTypeExpr (l, te, int_of_big_int size)
     | [< >] ->
       ArrayTypeExpr (l, te)
     end;
     '(_, Kwd "]") >] -> te
| [< >] -> te
and
  parse_decl_stmt_rest te lx x = parser
    [< '(l, Kwd "=");
       s = parser
         [< '(l, Kwd "create_handle"); '(_, Ident hpn); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd ";") >] ->
         begin
           match te with ManifestTypeExpr (_, HandleIdType) -> () | _ -> raise (ParseException (l, "Target variable of handle creation statement must have type 'handle'."))
         end;
         CreateHandleStmt (l, x, hpn, e)
       | [< rhs = parse_declaration_rhs te; ds = comma_rep (parse_declarator te); '(_, Kwd ";") >] ->
         DeclStmt (l, (l, te, x, Some(rhs), ref false)::ds)
    >] -> s
  | [< tx = parse_array_braces te;
       init = opt (parser [< '(_, Kwd "="); e = parse_declaration_rhs tx >] -> e);
       ds = comma_rep (parse_declarator te);
       '(_, Kwd ";")
    >] ->
    DeclStmt(type_expr_loc te, (lx, tx, x, init, ref false)::ds)
and
  parse_switch_stmt_clauses = parser
  [< c = parse_switch_stmt_clause; cs = parse_switch_stmt_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_stmt_clause = parser
  [< '(l, Kwd "case"); e = parse_expr; '(_, Kwd ":"); ss = parse_stmts >] -> SwitchStmtClause (l, e, ss)
| [< '(l, Kwd "default"); '(_, Kwd ":"); ss = parse_stmts; >] -> SwitchStmtDefaultClause(l, ss)
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
  [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_pred_clauses; '(_, Kwd "}") >] -> SwitchAsn (l, e, cs)
| [< '(l, Kwd "emp") >] -> EmpAsn l
| [< '(_, Kwd "("); p = parse_pred; '(_, Kwd ")") >] -> p
| [< '(l, Kwd "["); coef = parse_pattern; '(_, Kwd "]"); p = parse_pred0 >] -> CoefAsn (l, coef, p)
| [< '(_, Kwd "#"); '(l, String s) >] -> PluginAsn (l, s)
| [< e = parse_disj_expr; p = parser
    [< '(l, Kwd "|->"); rhs = parse_pattern >] -> PointsTo (l, e, rhs)
  | [< '(l, Kwd "?"); p1 = parse_pred; '(_, Kwd ":"); p2 = parse_pred >] -> IfAsn (l, e, p1, p2)
  | [< >] ->
    (match e with
     | CallExpr (l, g, targs, pats0, pats, Static) -> PredAsn (l, new predref g, targs, pats0, pats)
     | CallExpr (l, g, [], pats0, LitPat e::pats, Instance) ->
       let index =
         match pats0 with
           [] -> CallExpr (l, "getClass", [], [], [LitPat e], Instance)
         | [LitPat e] -> e
         | _ -> raise (ParseException (l, "Instance predicate call: single index expression expected"))
       in
       InstPredAsn (l, e, g, index, pats)
     | _ -> ExprAsn (expr_loc e, e)
    )
  >] -> p
and
  parse_pattern = parser
  [< '(_, Kwd "_") >] -> DummyPat
| [< '(_, Kwd "?"); '(lx, Ident x) >] -> VarPat x
| [< '(_, Kwd "^"); e = parse_expr >] -> LitPat (WidenedParameterArgument e)
| [< e = parse_expr >] -> LitPat e
and
  parse_switch_pred_clauses = parser
  [< c = parse_switch_pred_clause; cs = parse_switch_pred_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_pred_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); p = parse_pred; '(_, Kwd ";") >] -> SwitchAsnClause (l, c, pats, ref None, p)
and
  parse_expr stream = parse_assign_expr stream
and
  parse_assign_expr = parser
  [< e0 = parse_cond_expr; e = parse_assign_expr_rest e0 >] -> e
and
  parse_cond_expr = parser
  [< e0 = parse_disj_expr; e = parser
    [< '(l, Kwd "?"); e1 = parse_expr; '(_, Kwd ":"); e2 = parse_cond_expr >] -> IfExpr (l, e0, e1, e2)
  | [< >] -> e0
  >] -> e
and
  parse_disj_expr = parser
  [< e0 = parse_conj_expr; e = parse_disj_expr_rest e0 >] -> e
and
  parse_conj_expr = parser
  [< e0 = parse_bitor_expr; e = parse_conj_expr_rest e0 >] -> e
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
  [< e0 = parse_shift; e = parse_expr_rel_rest e0 >] -> e
and
  parse_shift = parser
  [< e0 = parse_expr_arith; e = parse_shift_rest e0 >] -> e
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
  parse_new_array_expr_rest l elem_typ = parser
  [< '(_, Kwd "[");
     e = parser
       [< length = parse_expr; '(_, Kwd "]"); >] -> NewArray(l, elem_typ, length)
     | [< '(_, Kwd "]"); '(_, Kwd "{"); es = rep_comma parse_expr; '(_, Kwd "}") >] -> NewArrayWithInitializer (l, elem_typ, es)
  >] -> e
and
  parse_expr_primary = parser
  [< '(l, Kwd "true") >] -> True l
| [< '(l, Kwd "false") >] -> False l
| [< '(l, CharToken c) >] -> IntLit(l, big_int_of_int (Char.code c), ref (Some Char))
| [< '(l, Kwd "null") >] -> Null l
| [< '(l, Kwd "currentThread") >] -> Var (l, "currentThread", ref None)
| [< '(l, Kwd "new"); tp = parse_primary_type; res = (parser 
                    [< args0 = parse_patlist >] -> 
                    begin match tp with
                      IdentTypeExpr(_, pac, cn) -> NewObject (l, (match pac with None -> "" | Some(pac) -> pac ^ ".") ^ cn, List.map (function LitPat e -> e | _ -> raise (Stream.Error "Patterns are not allowed in this position")) args0)
                    | _ -> raise (ParseException (type_expr_loc tp, "Class name expected"))
                    end
                  | [< e = parse_new_array_expr_rest l tp >] -> e)
  >] -> res
| [<
    '(lx, Ident x);
    ex = parser
      [<
        args0 = parse_patlist;
        e = parser
          [< args = parse_patlist >] -> CallExpr (lx, x, [], args0, args,Static)
        | [< >] -> CallExpr (lx, x, [], [], args0,Static)
      >] -> e
    | [<
        '(ldot, Kwd ".");
        r = parser
          [<'(lc, Kwd "class")>] -> ClassLit(ldot,x)
        | [<
            '(lf, Ident f);
            e = parser
              [<args0 = parse_patlist; (args0, args) = (parser [< args = parse_patlist >] -> (args0, args) | [< >] -> ([], args0)) >] ->
              CallExpr (lf, f, [], args0, LitPat(Var(lx,x,ref None))::args,Instance)
            | [<>] -> Read (ldot, Var(lx,x, ref None), f)
          >]->e 
      >]-> r
    | [< >] -> Var (lx, x, ref None)
  >] -> ex
| [< '(l, Int i) >] -> IntLit (l, i, ref None)
| [< '(l, RealToken i) >] -> RealLit (l, num_of_big_int i)
| [< '(l, Kwd "INT_MIN") >] -> IntLit (l, big_int_of_string "-2147483648", ref None)
| [< '(l, Kwd "INT_MAX") >] -> IntLit (l, big_int_of_string "2147483647", ref None)
| [< '(l, Kwd "UINTPTR_MAX") >] -> IntLit (l, big_int_of_string "4294967295", ref None)
| [< '(l, String s); ss = rep (parser [< '(_, String s) >] -> s) >] -> StringLit (l, String.concat "" (s::ss))
| [< '(l, Kwd "truncating"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, true, t, e)
| [< e = peek_in_ghost_range (parser [< '(l, Kwd "truncating"); '(_, Kwd "@*/"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, true, t, e)) >] -> e
| [< '(l, Kwd "(");
     e = parser
     [< e0 = parse_expr; '(_, Kwd ")");
         e = parser
           [< '(l', Ident y); e = parse_expr_suffix_rest (Var (l', y, ref (Some LocalVar))) >] -> (match e0 with 
             Var (lt, x, _) -> CastExpr (l, false, IdentTypeExpr (lt, None, x), e)
           | _ -> raise (ParseException (l, "Type expression of cast expression must be identifier: ")))
         | [<>] -> e0
     >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, false, te, e)
   >] -> e
(*
| [< '(l, Kwd "(");
     e = parser
     [< e = parse_expr; '(_, Kwd ")") >] -> e
   | [< te = parse_type; '(_, Kwd ")"); e = parse_expr_suffix >] -> CastExpr (l, te, e)
   >] -> e*)
| [< '(l, Kwd "switch"); '(_, Kwd "("); e = parse_expr; '(_, Kwd ")"); '(_, Kwd "{"); cs = parse_switch_expr_clauses;
     cdef_opt = opt (parser [< '(l, Kwd "default"); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> (l, e));
     '(_, Kwd "}")
  >] -> SwitchExpr (l, e, cs, cdef_opt, ref None)
| [< '(l, Kwd "sizeof"); '(_, Kwd "("); t = parse_type; '(_, Kwd ")") >] -> SizeofExpr (l, t)
| [< '(l, Kwd "super"); '(_, Kwd "."); '(l2, Ident n); '(_, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")") >] -> SuperMethodCall (l, n, es)
| [< '(l, Kwd "!"); e = parse_expr_suffix >] -> Operation(l, Not, [e], ref None)
| [< '(l, Kwd "@"); '(_, Ident g) >] -> PredNameExpr (l, g)
| [< '(l, Kwd "*"); e = parse_expr_suffix >] -> Deref (l, e, ref None)
| [< '(l, Kwd "&"); e = parse_expr_suffix >] -> AddressOf (l, e)
| [< '(l, Kwd "~"); e = parse_expr_suffix >] -> Operation (l, BitNot, [e], ref None)
| [< '(l, Kwd "-"); e = parse_expr_suffix >] ->
  begin match e with
    IntLit (_, n, t) -> IntLit (l, minus_big_int n, t)
  | _ -> Operation (l, Sub, [IntLit (l, zero_big_int, ref None); e], ref None)
  end
| [< '(l, Kwd "++"); e = parse_expr_suffix >] -> AssignOpExpr (l, e, Add, IntLit (l, unit_big_int, ref None), false, ref None, ref None)
| [< '(l, Kwd "--"); e = parse_expr_suffix >] -> AssignOpExpr (l, e, Sub, IntLit (l, unit_big_int, ref None), false, ref None, ref None)
| [< '(l, Kwd "{"); es = rep_comma parse_expr; '(_, Kwd "}") >] -> InitializerList (l, es)
and
  parse_switch_expr_clauses = parser
  [< c = parse_switch_expr_clause; cs = parse_switch_expr_clauses >] -> c::cs
| [< >] -> []
and
  parse_switch_expr_clause = parser
  [< '(l, Kwd "case"); '(_, Ident c); pats = (parser [< '(_, Kwd "("); '(lx, Ident x); xs = parse_more_pats >] -> x::xs | [< >] -> []); '(_, Kwd ":"); '(_, Kwd "return"); e = parse_expr; '(_, Kwd ";") >] -> SwitchExprClause (l, c, pats, e)
and
  expr_to_class_name e =
    match e with
      Var (_, x, _) -> x
    | Read (_, e, f) -> expr_to_class_name e ^ "." ^ f
    | _ -> raise (ParseException (expr_loc e, "Class name expected"))
and
  parse_expr_suffix_rest e0 = parser
  [< '(l, Kwd "->"); '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, f)) >] -> e
| [< '(l, Kwd ".");
     e = begin parser
       [< '(_, Ident f); e = parse_expr_suffix_rest (Read (l, e0, f)) >] -> e
     | [< '(_, Kwd "class"); e = parse_expr_suffix_rest (ClassLit (l, expr_to_class_name e0)) >] -> e
     end
  >] -> e
| [< '(l, Kwd "["); 
     e = begin parser
       [< '(_, Kwd "]") >] -> ArrayTypeExpr' (l, e0)
     | [< e1 = parse_expr; '(l, Kwd "]") >] -> ReadArray (l, e0, e1)
     end; e = parse_expr_suffix_rest e >] -> e
| [< '(l, Kwd "++"); e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Add, IntLit (l, unit_big_int, ref None), true, ref None, ref None)) >] -> e
| [< '(l, Kwd "--"); e = parse_expr_suffix_rest (AssignOpExpr (l, e0, Sub, IntLit (l, unit_big_int, ref None), true, ref None, ref None)) >] -> e
| [< '(l, Kwd "("); es = rep_comma parse_expr; '(_, Kwd ")"); e = parse_expr_suffix_rest (match e0 with Read(l', e0', f') -> CallExpr (l', f', [], [], LitPat(e0'):: (List.map (fun e -> LitPat(e)) es), Instance) | _ -> ExprCallExpr (l, e0, es)) >] -> e
| [< >] -> e0
and
  parse_expr_mul_rest e0 = parser
  [< '(l, Kwd "*"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Mul, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "/"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Div, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "%"); e1 = parse_expr_suffix; e = parse_expr_mul_rest (Operation (l, Mod, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_expr_arith_rest e0 = parser
  [< '(l, Kwd "+"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Add, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "-"); e1 = parse_expr_mul; e = parse_expr_arith_rest (Operation (l, Sub, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_shift_rest e0 = parser
  [< '(l, Kwd "<<"); e1 = parse_expr_arith; e = parse_shift_rest (Operation (l, ShiftLeft, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd ">>"); e1 = parse_expr_arith; e = parse_shift_rest (Operation (l, ShiftRight, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and

  parse_expr_rel_rest e0 = parser
  [< '(l, Kwd "=="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Eq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "!="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Neq, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd "<="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e0; e1], ref None)) >] -> e
| [< '(l, Kwd ">"); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Lt, [e1; e0], ref None)) >] -> e
| [< '(l, Kwd ">="); e1 = parse_expr_arith; e = parse_expr_rel_rest (Operation (l, Le, [e1; e0], ref None)) >] -> e
| [< '(l, Kwd "instanceof"); tp = parse_expr; e = parse_expr_rel_rest (InstanceOfExpr (l, e0, type_expr_of_expr tp)) >] -> e
| [< e = parse_expr_lt_rest e0 parse_expr_rel_rest >] -> e
and
  apply_type_args e targs args =
  match e with
    Var (lx, x, _) -> CallExpr (lx, x, targs, [], args, Static)
  | CastExpr (lc, trunc, te, e) -> CastExpr (lc, trunc, te, apply_type_args e targs args)
  | Operation (l, Not, [e], ts) -> Operation (l, Not, [apply_type_args e targs args], ts)
  | Operation (l, BitNot, [e], ts) -> Operation (l, BitNot, [apply_type_args e targs args], ts)
  | Deref (l, e, ts) -> Deref (l, apply_type_args e targs args, ts)
  | AddressOf (l, e) -> AddressOf (l, apply_type_args e targs args)
  | Operation (l, op, [e1; e2], ts) -> Operation (l, op, [e1; apply_type_args e2 targs args], ts)
  | _ -> raise (ParseException (expr_loc e, "Identifier expected before type argument list"))
and
  parse_expr_lt_rest e0 cont = parser
  [< '(l, Kwd "<");
     e = parser
       [< e1 = parse_expr_arith; e1 = parse_expr_lt_rest e1 (let rec iter e0 = parse_expr_lt_rest e0 iter in iter);
          e = parser
            [< '(_, Kwd ">"); (* Type argument *)
               args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
               e = cont (apply_type_args e0 [type_expr_of_expr e1] args)
            >] -> e
          | [< '(_, Kwd ","); ts = rep_comma parse_type; '(_, Kwd ">");
               args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
               e = cont (apply_type_args e0 ([type_expr_of_expr e1] @ ts) args)
            >] -> e
          | [< e = cont (Operation (l, Lt, [e0; e1], ref None)) >] -> e
       >] -> e
     | [< ts = rep_comma parse_type; '(_, Kwd ">");
          args = (parser [< args = parse_patlist >] -> args | [< >] -> []);
          e = cont (apply_type_args e0 ts args)
       >] -> e
  >] -> e
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
  parse_conj_expr_rest e0 = parser
  [< '(l, Kwd "&&"); e1 = parse_expr_rel; e = parse_conj_expr_rest (Operation (l, And, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_disj_expr_rest e0 = parser
  [< '(l, Kwd "||"); e1 = parse_conj_expr; e = parse_disj_expr_rest (Operation (l, Or, [e0; e1], ref None)) >] -> e
| [< >] -> e0
and
  parse_assign_expr_rest e0 = parser
  [< '(l, Kwd "="); e1 = parse_assign_expr >] -> AssignExpr (l, e0, e1)
| [< '(l, Kwd "+="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Add, e1, false, ref None, ref None)
| [< '(l, Kwd "-="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Sub, e1, false, ref None, ref None)
| [< '(l, Kwd "*="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Mul, e1, false, ref None, ref None)
| [< '(l, Kwd "/="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Div, e1, false, ref None, ref None)
| [< '(l, Kwd "&="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, And, e1, false, ref None, ref None)
| [< '(l, Kwd "|="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Or, e1, false, ref None, ref None)
| [< '(l, Kwd "^="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Xor, e1, false, ref None, ref None)
| [< '(l, Kwd "%="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, Mod, e1, false, ref None, ref None)
| [< '(l, Kwd "<<="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ShiftLeft, e1, false, ref None, ref None)
| [< '(l, Kwd ">>="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ShiftRight, e1, false, ref None, ref None)
(*| [< '(l, Kwd ">>>="); e1 = parse_assign_expr >] -> AssignOpExpr (l, e0, ???, e1, false, ref None, ref None)*)
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
  [< (l,p) = parse_package; is=rep parse_import; ds=parse_decls;>] -> PackageDecl(l,p,Import(dummy_loc,"java.lang",None)::is, ds)

let parse_scala_file (path: string) (reportRange: range_kind -> loc -> unit): package =
  let lexer = make_lexer Scala.keywords ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange (fun x->()) in
  let parse_decls_eof = parser [< ds = rep Scala.parse_decl; _ = Stream.empty >] -> PackageDecl(dummy_loc,"",[Import(dummy_loc,"java.lang",None)],ds) in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))

let parse_java_file (path: string) (reportRange: range_kind -> loc -> unit) reportShouldFail: package =
  Stopwatch.start parsing_stopwatch;
  let result =
  if Filename.check_suffix (Filename.basename path) ".scala" then
    parse_scala_file path reportRange
  else
  let lexer = make_lexer (common_keywords @ java_keywords) ghost_keywords in
  let (loc, ignore_eol, token_stream) = lexer (Filename.dirname path, Filename.basename path) (readFile path) reportRange reportShouldFail in
  let parse_decls_eof = parser [< p = parse_package_decl; _ = Stream.empty >] -> p in
  try
    parse_decls_eof token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

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

let parse_c_file (path: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit) (runPreprocessor: bool): ((loc * string) list * package list) = (* ?parse_c_file *)
  Stopwatch.start parsing_stopwatch;
  let result =
  let make_lexer basePath relPath =
    let text = readFile (Filename.concat basePath relPath) in
    make_lexer (common_keywords @ c_keywords) ghost_keywords (basePath, relPath) text reportRange reportShouldFail
  in
  let make_lexer = if runPreprocessor then make_preprocessor make_lexer else make_lexer in
  let (loc, ignore_eol, token_stream) = make_lexer (Filename.dirname path) (Filename.basename path) in
  let parse_c_file =
    parser
      [< headers = parse_include_directives ignore_eol; ds = parse_decls; _ = Stream.empty >] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
  in
  try
    parse_c_file token_stream
  with
    Stream.Error msg -> raise (ParseException (loc(), msg))
  | Stream.Failure -> raise (ParseException (loc(), "Parse error"))
  in
  Stopwatch.stop parsing_stopwatch;
  result

let parse_header_file (basePath: string) (relPath: string) (reportRange: range_kind -> loc -> unit) (reportShouldFail: loc -> unit): ((loc * string) list * package list) =
  Stopwatch.start parsing_stopwatch;
  let result =
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
  let pos = ((Filename.dirname path, Filename.basename path), 1, 1) in
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

let path_macros = [("VERIFAST", rtdir)]

let expand_path path =
  expand_macros path_macros path

let concat_if_relative path1 path2 =
  if Filename.is_relative path2 then
    Filename.concat path1 path2
  else
    path2

let parse_jarspec_file_core path =
  let dirPath = Filename.dirname path in
  let lines = read_file_lines path in
  let (jarspecs, lines) =
    let rec iter jarspecs lines =
      match lines with
      | line::lines when line = "" ->
        iter jarspecs lines
      | line::lines when Filename.check_suffix line ".jarspec" ->
        iter (concat_if_relative dirPath (expand_path line)::jarspecs) lines
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
          raise (ParseException (file_loc path, "A .jarspec file must consists of a list of .jarspec file paths followed by a list of .javaspec file paths"))
        else
          [Filename.concat dirPath line]
      end
      lines
  in
  (jarspecs, javaspecs)

let parse_jarsrc_file_core path =
  let dirPath = Filename.dirname path in
  let lines = read_file_lines path in
  let (jars, lines) =
    let rec iter jars lines =
      match lines with
        line::lines when not (startswith line "main-class ") && Filename.check_suffix line ".jar" ->
        iter (concat_if_relative dirPath (expand_path line)::jars) lines
      | _ ->
        (List.rev jars, lines)
    in
    iter [] lines
  in
  let (javas, lines) =
    let rec iter javas lines =
      match lines with
        line::lines when not (startswith line "main-class ") && Filename.check_suffix line ".java" ->
        iter (Filename.concat dirPath line::javas) lines
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
      provides @ ["main_class " ^ mainClass]
    | _ ->
      raise (ParseException (file_loc path, "A .jarsrc file must consists of a list of .jar file paths followed by a list of .java file paths, optionally followed by a line of the form \"main-class mymainpackage.MyMainClass\""))
  in
  (jars, javas, provides)

(* Region: some auxiliary types and functions *)

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

let is_lemma k = match k with Lemma(_) -> true | _ -> false

let printff format = kfprintf (fun _ -> flush stdout) stdout format

(** Internal pattern. Either a pattern from the source code, or a term pattern. A term pattern (TermPat t) matches a term t' if t and t' are definitely_equal. *)
type 'termnode pat0 = SrcPat of pat | TermPat of 'termnode
(** A heap chunk. *)
type chunk_info =
  PredicateChunkSize of int (* Size of this chunk with respect to the first chunk of the precondition; used to check lemma termination. *)
| PluginChunkInfo of Plugins.plugin_state
type 'termnode chunk =
  Chunk of
    ('termnode (* Predicate name *) * bool (* true if a declared predicate's symbol; false in a scenario where predicate names are passed as values. Used to avoid prover queries. *) ) *
    type_ list *  (* Type arguments *)
    'termnode *  (* Coefficient of fractional permission *)
    'termnode list *  (* Arguments; their prover type is as per the instantiated parameter types, not the generic ones. *)
    chunk_info option
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
  | UShortType -> "ushort"
  | ShortType -> "short"
  | UintPtrType -> "uintptr_t"
  | RealType -> "real"
  | UChar -> "uint8"
  | Char -> "int8"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
  | ObjType l -> "class " ^ l
  | StructType sn -> "struct " ^ sn
  | PtrType t -> string_of_type t ^ " *"
  | FuncType ft -> ft
  | PredType (tparams, ts, inputParamCount) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    Printf.sprintf "predicate%s(%s)" tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fixpoint(%s, %s)" (String.concat ", " (List.map string_of_type pts)) (string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | TypeParam x -> x
  | InferredType t -> begin match !t with None -> "?" | Some t -> string_of_type t end
  | ArrayType(t) -> (string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> (string_of_type t) ^ "[" ^ (string_of_int s) ^ "]" 
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (string_of_type t)

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

exception SymbolicExecutionError of string context list * string * loc * string * string option

let full_name pn n = if pn = "" then n else pn ^ "." ^ n

type options = {
  option_verbose: int;
  option_disable_overflow_check: bool;
  option_allow_should_fail: bool;
  option_emit_manifest: bool;
  option_allow_assume: bool;
  option_simplify_terms: bool;
  option_runtime: string option;
  option_run_preprocessor: bool;
  option_provides: string list;
  option_keep_provide_files: bool
} (* ?options *)

(* Region: verify_program_core: the toplevel function *)

(** Verifies the .c/.jarsrc/.scala file at path [path].
    Uses the SMT solver [ctxt].
    Reports syntax highlighting regions using the callback [reportRange].
    Stops at source line [breakpoint], if not None.
    This function is generic in the types of SMT solver types, symbols, and terms.
    *)
let verify_program_core (* ?verify_program_core *)
    ?(emitter_callback : package list -> unit = fun _ -> ())
    (type typenode) (type symbol) (type termnode)  (* Explicit type parameters; new in OCaml 3.12 *)
    (ctxt: (typenode, symbol, termnode) Proverapi.context)
    (options : options)
    (program_path : string)
    (reportRange : range_kind -> loc -> unit)
    (reportUseSite : decl_kind -> loc -> loc -> unit)
    (breakpoint : (string * int) option) : unit =
  
  let path = program_path in
  
  let language = file_type path in
  
  let auto_lemmas = Hashtbl.create 10 in

  let {
    option_verbose=initial_verbosity;
    option_disable_overflow_check=disable_overflow_check;
    option_allow_should_fail=allow_should_fail;
    option_emit_manifest=emit_manifest
  } = options in
  
  let verbosity = ref 0 in
  
  let set_verbosity v =
    verbosity := v;
    ctxt#set_verbosity (v - 3)
  in
  
  set_verbosity initial_verbosity;
  
  let class_counter = ref 0 in

  (** Maps an identifier to a ref cell containing approximately the number of distinct symbols that have been generated for this identifier.
    * It is an approximation because of clashes such as the clash between the second symbol ('foo0') generated for 'foo'
    * and the first symbol ('foo0') generated for 'foo0'. *)
  let used_ids = Hashtbl.create 10000 in
  (** Contains all ref cells from used_ids that need to be decremented at the next pop(). *)
  let used_ids_undo_stack = ref [] in
  (** The terms that represent coefficients of leakable chunks. These come from [_] patterns in the source code. *)
  let dummy_frac_terms = ref [] in
  (** When switching to the next symbolic execution branch, this stack is popped to forget about fresh identifiers generated in the old branch. *)
  let used_ids_stack = ref [] in

  (** Remember the current path condition, set of used IDs, and set of dummy fraction terms. *)  
  let push() =
    used_ids_stack := (!used_ids_undo_stack, !dummy_frac_terms)::!used_ids_stack;
    used_ids_undo_stack := [];
    ctxt#push
  in
  
  (** Restore the previous path condition, set of used IDs, and set of dummy fraction terms. *)
  let pop() =
    List.iter (fun r -> decr r) !used_ids_undo_stack;
    let ((usedIdsUndoStack, dummyFracTerms)::t) = !used_ids_stack in
    used_ids_undo_stack := usedIdsUndoStack;
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
  
  let get_ident_use_count_cell s =
    try
      Hashtbl.find used_ids s
    with Not_found ->
      let cell = ref 0 in
      Hashtbl.add used_ids s cell;
      cell
  in
  
  (** Generate a fresh ID based on string [s]. *)
  let mk_ident s =
    let count_cell = get_ident_use_count_cell s in
    let rec find_unused_ident count =
      count_cell := count + 1;
      used_ids_undo_stack := count_cell::!used_ids_undo_stack;
      if count = 0 then
        s
      else
        let s = Printf.sprintf "%s%d" s (count - 1) in
        let indexed_count_cell = get_ident_use_count_cell s in
        if !indexed_count_cell > 0 then
          find_unused_ident (count + 1)
        else begin
          indexed_count_cell := 1;
          used_ids_undo_stack := indexed_count_cell::!used_ids_undo_stack;
          s
        end
    in
    find_unused_ident !count_cell
  in
  
  (** Convert term [t] from type [proverType] to type [proverType0]. *)  
  let apply_conversion proverType proverType0 t =
    match (proverType, proverType0) with
    | (ProverBool, ProverInductive) -> ctxt#mk_boxed_bool t
    | (ProverInt, ProverInductive) -> ctxt#mk_boxed_int t
    | (ProverReal, ProverInductive) -> ctxt#mk_boxed_real t
    | (ProverInductive, ProverBool) -> ctxt#mk_unboxed_bool t
    | (ProverInductive, ProverInt) -> ctxt#mk_unboxed_int t
    | (ProverInductive, ProverReal) -> ctxt#mk_unboxed_real t
    | (t1, t2) when t1 = t2 -> t
  in
  
  let typenode_of_provertype t =
    match t with
      ProverInt -> ctxt#type_int
    | ProverBool -> ctxt#type_bool
    | ProverReal -> ctxt#type_real
    | ProverInductive -> ctxt#type_inductive
  in
  
  let mk_symbol s domain range kind =
    ctxt#mk_symbol (mk_ident s) domain range kind
  in

  (** For higher-order function application *)
  let apply_symbol = ctxt#mk_symbol "@" [ctxt#type_inductive; ctxt#type_inductive] ctxt#type_inductive Uninterp in

  (** Generate a fresh SMT solver symbol based on string [s]. *)  
  let mk_func_symbol s domain range kind =
    let s = mk_ident s in
    let domain_tnodes = List.map typenode_of_provertype domain in
    let fsymb = ctxt#mk_symbol s domain_tnodes (typenode_of_provertype range) kind in
    if domain = [] then
      (fsymb, ctxt#mk_app fsymb [])
    else
      let vsymb = ctxt#mk_app (ctxt#mk_symbol ("@" ^ s) [] ctxt#type_inductive Uninterp) [] in
      (* Emit an axiom saying that @(@f, x) == f(x) / @(@(@f, x), y) == f(x, y) / ... *)
      ctxt#begin_formal;
      let bounds = imap (fun k t -> ctxt#mk_bound k t) domain_tnodes in
      let app = List.fold_left2 (fun t1 tp t2 -> ctxt#mk_app apply_symbol [t1; apply_conversion tp ProverInductive t2]) vsymb domain bounds in
      let body = ctxt#mk_eq (apply_conversion ProverInductive range app) (ctxt#mk_app fsymb bounds) in
      ctxt#end_formal;
      ctxt#assume_forall [app] domain_tnodes body;
      (fsymb, vsymb)
  in
  
  let mk_app (fsymb, vsymb) ts =
    ctxt#mk_app fsymb ts
  in
  
  (* Region: boxing and unboxing *)
  
  let rec provertype_of_type t =
    match t with
      Bool -> ProverBool
    | IntType -> ProverInt
    | UShortType -> ProverInt
    | ShortType -> ProverInt
    | UintPtrType -> ProverInt
    | RealType -> ProverReal
    | UChar -> ProverInt
    | Char -> ProverInt
    | InductiveType _ -> ProverInductive
    | StructType sn -> assert false
    | ObjType n -> ProverInt
    | ArrayType t -> ProverInt
    | StaticArrayType (t, s) -> ProverInt
    | PtrType t -> ProverInt
    | FuncType _ -> ProverInt
    | PredType (tparams, ts, inputParamCount) -> ProverInductive
    | PureFuncType _ -> ProverInductive
    | BoxIdType -> ProverInt
    | HandleIdType -> ProverInt
    | AnyType -> ProverInductive
    | TypeParam _ -> ProverInductive
    | Void -> ProverInductive
    | InferredType t -> begin match !t with None -> t := Some (InductiveType ("unit", [])); ProverInductive | Some t -> provertype_of_type t end
  in
  
  let typenode_of_type t = typenode_of_provertype (provertype_of_type t) in
   
  (* Generate some global symbols. *)
  
  let get_class_symbol = mk_symbol "getClass" [ctxt#type_int] ctxt#type_int Uninterp in
  let class_serial_number = mk_symbol "class_serial_number" [ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_or_symbol = mk_symbol "bitor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_xor_symbol = mk_symbol "bitxor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_and_symbol = mk_symbol "bitand" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp in
  let bitwise_not_symbol = mk_symbol "bitnot" [ctxt#type_int] ctxt#type_int Uninterp in
  let arraylength_symbol = mk_symbol "arraylength" [ctxt#type_int] ctxt#type_int Uninterp in
  let shiftleft_int32_symbol = mk_symbol "shiftleft_int32" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp in (* shift left and truncate to 32-bit signed integer; Java's "<<" operator on two ints *)
  let shiftright_symbol = mk_symbol "shiftright" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp in (* shift right with sign extension; Java's ">>" operator. For nonnegative n, "x >> n" is equivalent to floor(x / 2^n). *)
  let truncate_int8_symbol = mk_symbol "truncate_int8" [ctxt#type_int] ctxt#type_int Uninterp in
  let truncate_int16_symbol = mk_symbol "truncate_int16" [ctxt#type_int] ctxt#type_int Uninterp in
  
  ignore $. ctxt#assume (ctxt#mk_eq (ctxt#mk_unboxed_bool (ctxt#mk_boxed_int (ctxt#mk_intlit 0))) ctxt#mk_false); (* This allows us to use 0 as a default value for all types; see the treatment of array creation. *)

  let boolt = Bool in
  let intt = IntType in
  let instanceof_symbol = ctxt#mk_symbol "instanceof" [ctxt#type_int; ctxt#type_int] ctxt#type_bool Uninterp in
  let array_type_symbol = ctxt#mk_symbol "array_type"  [ctxt#type_int] ctxt#type_int Uninterp in
  
  let two_big_int = big_int_of_int 2 in
  
  let real_zero = ctxt#mk_reallit 0 in
  let real_unit = ctxt#mk_reallit 1 in
  let real_half = ctxt#mk_reallit_of_num (num_of_ints 1 2) in

  let int_zero_term = ctxt#mk_intlit 0 in 

  (* unsigned int & pointer types *)
  let min_uint_term = ctxt#mk_intlit_of_string "0" in
  let max_uint_term = ctxt#mk_intlit_of_string "4294967295" in
  let min_ptr_big_int = big_int_of_string "0" in
  let max_ptr_big_int = big_int_of_string "4294967295" in
  let max_ptr_term = ctxt#mk_intlit_of_string "4294967295" in

  (* signed int *)
  let min_int_big_int = big_int_of_string "-2147483648" in
  let min_int_term = ctxt#mk_intlit_of_string "-2147483648" in
  let max_int_big_int = big_int_of_string "2147483647" in
  let max_int_term = ctxt#mk_intlit_of_string "2147483647" in

  (* unsigned short *)
  let min_ushort_big_int = big_int_of_string "0" in
  let min_ushort_term = ctxt#mk_intlit_of_string "0" in
  let max_ushort_big_int = big_int_of_string "65535" in
  let max_ushort_term = ctxt#mk_intlit_of_string "65535" in

  (* signed short *)
  let min_short_big_int = big_int_of_string "-32768" in
  let min_short_term = ctxt#mk_intlit_of_string "-32768" in
  let max_short_big_int = big_int_of_string "32767" in
  let max_short_term = ctxt#mk_intlit_of_string "32767" in

  (* unsigned char *)
  let min_uchar_big_int = big_int_of_string "0" in
  let min_uchar_term = ctxt#mk_intlit_of_string "0" in
  let max_uchar_big_int = big_int_of_string "255" in
  let max_uchar_term = ctxt#mk_intlit_of_string "255" in

  (* signed char *)
  let min_char_big_int = big_int_of_string "-128" in
  let min_char_term = ctxt#mk_intlit_of_string "-128" in
  let max_char_big_int = big_int_of_string "127" in
  let max_char_term = ctxt#mk_intlit_of_string "127" in
  
  let get_unique_var_symb x t = 
    ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) []
  in
  let assume_bounds term tp = 
    match tp with
      Char -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_char_term term) (ctxt#mk_le term max_char_term));
    | ShortType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_short_term term) (ctxt#mk_le term max_short_term));
    | IntType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_int_term term) (ctxt#mk_le term max_int_term));
    | PtrType _ | UintPtrType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) term) (ctxt#mk_le term max_ptr_term));
    | _ -> ()
  in
  let get_unique_var_symb_non_ghost x t = 
    let res = get_unique_var_symb x t in
    assume_bounds res t;
    res
  in
  let get_unique_var_symb_ x t ghost = 
    if ghost then
      get_unique_var_symb x t
    else
      get_unique_var_symb_non_ghost x t
  in
  
  let get_dummy_frac_term () =
    let t = get_unique_var_symb "dummy" RealType in
    dummy_frac_terms := t::!dummy_frac_terms;
    t
  in
  
  let is_dummy_frac_term t = List.memq t !dummy_frac_terms in
  
  let get_unique_var_symbs xts = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) xts in
  let get_unique_var_symbs_ xts ghost = List.map (fun (x, t) -> (x, get_unique_var_symb_ x t ghost)) xts in
  let get_unique_var_symbs_non_ghost xts = List.map (fun (x, t) -> (x, get_unique_var_symb_non_ghost x t)) xts in
  
  let real_unit_pat = TermPat real_unit in
  
  let plugin_context = object
    method mk_symbol x tp = get_unique_var_symb x (match tp with Plugins.PointerTerm -> PtrType Void | Plugins.IntTerm -> IntType | Plugins.CharListTerm -> InductiveType ("list", [IntType]))
    method query_formula t1 r t2 = ctxt#query (match r with Plugins.Eq -> ctxt#mk_eq t1 t2 | Plugins.Neq -> ctxt#mk_not (ctxt#mk_eq t1 t2) | Plugins.Lt -> ctxt#mk_lt t1 t2)
    method push = ctxt#push
    method assert_formula t1 r t2 = ctxt#assume (match r with Plugins.Eq -> ctxt#mk_eq t1 t2 | Plugins.Neq -> ctxt#mk_not (ctxt#mk_eq t1 t2) | Plugins.Lt -> ctxt#mk_lt t1 t2) = Unsat
    method pop = ctxt#pop
  end in
  
  let current_module_name =
    match language with
      | Java -> "current_module"
      | CLang -> Filename.chop_extension (Filename.basename path)
  in
  let current_module_term = get_unique_var_symb current_module_name IntType in
  let modulemap = [(current_module_name, current_module_term)] in
  
  let programDir = Filename.dirname path in
  let preludePath = Filename.concat bindir "prelude.h" in
  let rtpath = match options.option_runtime with None -> Filename.concat rtdir "rt.jarspec" | Some path -> path in
  (** Records the source lines containing //~, indicating that VeriFast is supposed to detect an error on that line. *)
  let shouldFailLocs = ref [] in
  
  (* Callback function called from the lexer. *)
  let reportShouldFail l =
    if allow_should_fail then
      shouldFailLocs := l::!shouldFailLocs
    else
      static_error l "Should fail directives are not allowed; use the -allow_should_fail command-line option to allow them." None
  in
  
  let check_should_fail default body =
    let locs_match ((path0, line0, _), _) ((path1, line1, _), _) = path0 = path1 && line0 = line1 in
    let should_fail l = List.exists (locs_match l) !shouldFailLocs in
    let has_failed l = shouldFailLocs := remove (locs_match l) !shouldFailLocs; default in
    let loc_of_ctxts ctxts l = match get_root_caller ctxts with None -> l | Some l -> l in
    try
      body ()
    with
    | StaticError (l, msg, url) when should_fail l -> has_failed l
    | SymbolicExecutionError (ctxts, phi, l, msg, url) when should_fail (loc_of_ctxts ctxts l) -> has_failed (loc_of_ctxts ctxts l)
  in
 
  let prototypes_used : (string * loc) list ref = ref [] in
  
  let register_prototype_used l g =
    if not (List.mem (g, l) !prototypes_used) then
      prototypes_used := (g, l)::!prototypes_used
  in
  
  let extract_specs ps=
    let rec iter (pn,ilist) classes lemmas ds=
      match ds with
      [] -> (classes,lemmas)
    | Class (l, abstract, fin, cn, meths, fds, cons, super, inames, preds)::rest ->
      let cn = full_name pn cn in
      let meths' = meths |> List.filter begin
        fun x ->
          match x with
            | Meth(lm, gh, t, n, ps, co, ss,fb,v,abstract) ->
              match ss with
                | None -> true
                | Some _ -> false
      end in
      (* TODO: cons' is not used anywhere, and should probably be used
         in the line after the definition. Changing it has no effect on the test results,
         clearly meaning that more tests should be written. I left it unchanged so that a warning still reminds us of this issue. *)
      let cons' = cons |> List.filter begin
        fun x ->
          match x with
            | Cons (lm, ps, co, ss, v) ->
              match ss with
                | None -> true
                | Some _ -> false
      end in
      iter (pn,ilist) (Class(l,abstract,fin,cn,meths',fds,cons,super,inames,[])::classes) lemmas rest
    | Func(l,Lemma(_),tparams,rt,fn,arglist,nonghost_callers_only,ftype,contract,None,fb,vis) as elem ::rest->
      let fn = full_name pn fn in
      iter (pn, ilist) classes (elem::lemmas) rest
    | _::rest -> 
      iter (pn, ilist) classes lemmas rest
    in
    let rec iter' (classes,lemmas) ps=
      match ps with
        PackageDecl(l,pn,ilist,ds)::rest-> iter' (iter (pn,ilist) classes lemmas ds) rest
      | [] -> (classes,lemmas)
    in
    iter' ([],[]) ps
  in
  
  (* Region: check_file *)
  
  let module CheckFileTypes = struct
    type 'a map = (string * 'a) list
    type struct_field_info =
        loc
      * ghostness
      * type_
    type struct_info =
        loc
      * (string * struct_field_info) list option (* None if struct without body *)
      * termnode option (* predicate symbol for struct_padding predicate *)
    type enum_info =
        big_int
    type global_info =
        loc
      * type_
      * termnode (* address symbol *)
      * expr option ref (* initializer *)
    type func_symbol =
        symbol
      * termnode (* function as value (for use with "apply") *)
    type pure_func_info =
        loc
      * string list (* type parameters *)
      * type_ (* return type *)
      * type_ list (* parameter types *)
      * func_symbol
    type inductive_ctor_info =
        string (* fully qualified constructor name *)
      * pure_func_info
    type inductive_info =
        loc
      * string list (* type parameters *)
      * (string * inductive_ctor_info) list
      * string list option (* The type is infinite if any of these type parameters are infinite; if None, it is always infinite. *)
    type pred_ctor_info =
      PredCtorInfo of
        loc
      * (string * type_) list (* constructor parameters *)
      * (string * type_) list (* predicate parameters *)
      * asn (* body *)
      * func_symbol
    type pred_fam_info =
        loc
      * string list (* type parameters *)
      * int (* number of predicate family indices *)
      * type_ list (* parameter types *)
      * termnode
      * int option (* number of input parameters; None if not precise *)
    type malloc_block_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type field_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type pred_inst_info =
        (string * termnode) list (* environment at definition site (for local predicate family instances; see e.g. examples/mcas/mcas.c) *)
      * loc
      * string list (* type parameters *)
      * (string * type_) list (* parameters *)
      * termnode (* predicate family symbol *)
      * int option (* input parameter count *)
      * asn (* body *)
    type pred_inst_map = ((string * string list) (* predicate name and indices *) * pred_inst_info) list
    type func_info =
      FuncInfo of
        (string * termnode) list (* environment at definition site (for local lemma functions) *)
      * termnode option (* function pointer; None if ? *)
      * loc
      * func_kind
      * string list (* type parameters *)
      * type_ option
      * (string * type_) list (* parameters *)
      * bool (* nonghost_callers_only *)
      * asn (* precondition *)
      * (string * type_) list (* type environment after precondition *)
      * asn (* postcondition *)
      * (string * pred_fam_info map * type_ list * (loc * string) list) option (* implemented function type, with function type type arguments and function type arguments *)
      * (stmt list * loc (* closing brace *) ) option option (* body; None if prototype; Some None if ? *)
      * method_binding (* always Static; TODO: remove *)
      * visibility (* always Public; TODO: remove *)
    type func_type_info =
        loc
      * ghostness
      * string list (* type parameters *)
      * type_ option (* return type *)
      * type_ map (* parameters of the function type *)
      * type_ map (* parameters of the function *)
      * asn (* precondition *)
      * asn (* postcondition *)
      * pred_fam_info map (* the is_xyz predicate, if any *)
    type signature = string * type_ list
    type method_info =
        loc
      * ghostness
      * type_ option
      * type_ map (* parameters *)
      * asn (* precondition *)
      * type_ map (* type environment after precondition *)
      * asn (* postcondition *)
      * (type_ * asn) list (* throws clauses *)
      * asn (* dynamic precondition (= precondition for dynamically bound calls) *)
      * asn (* dynamic postcondition (= postcondition for dynamically bound calls) *)
      * (type_ * asn) list (* dynamic throws clauses *)
      * (stmt list * loc) option option (* body *)
      * method_binding
      * visibility
      * bool (* is override *)
      * bool (* is abstract *)
    type interface_method_info =
        loc
      * ghostness
      * type_ option (* return type *)
      * type_ map (* parameters *)
      * asn (* precondition *)
      * type_ map (* type environment after precondition *)
      * asn (* postcondition *)
      * (type_ * asn) list (* throws clauses *)
      * visibility
      * bool (* is abstract *)
    type field_info = {
        fl: loc;
        fgh: ghostness;
        ft: type_;
        fvis: visibility;
        fbinding: method_binding;
        ffinal: bool;
        finit: expr option;
        fvalue: constant_value option option ref
      }
    type ctor_info =
        loc
      * type_ map (* parameters *)
      * asn
      * type_ map
      * asn
      * (type_ * asn) list
      * (stmt list * loc) option option
      * visibility
    type inst_pred_info =
        loc
      * type_ map
      * string (* family (= class or interface that first declared the predicate) *)
      * termnode
      * asn option
    type interface_inst_pred_info =
        loc
      * type_ map (* parameters *)
      * string (* family (= class or interface that first declared the predicate) *)
      * termnode (* predicate symbol *)
    type interface_info =
      InterfaceInfo of
        loc
      * field_info map
      * (signature * interface_method_info) list
      * interface_inst_pred_info map
      * string list (* superinterfaces *)
    type class_info = {
      cl: loc;
      cabstract: bool;
      cfinal: class_finality;
      cmeths: (signature * method_info) list;
      cfds: field_info map;
      cctors: (type_ list * ctor_info) list;
      csuper: string;
      cinterfs: string list;
      cpreds: inst_pred_info map;
      cpn: string; (* package *)
      cilist: import list
    }
    type plugin_info = (* logic plugins, e.g. to enable the use of Philippa Gardner's context logic for reasoning about tree data structures *)
        (  Plugins.plugin
         * termnode Plugins.plugin_instance)
      * termnode (* predicate symbol for plugin chunk *)
    type box_action_info =
        loc
      * type_ map (* parameters *)
      * expr (* precondition *)
      * expr (* postcondition *)
    type box_handle_predicate_info =
        loc
      * type_ map (* parameters *)
      * expr (* invariant *)
      * preserved_by_clause list
    type box_info = (* shared boxes *)
        loc
      * type_ map (* box parameters *)
      * asn (* invariant *)
      * type_ map (* variables bound by invariant *)
      * box_action_info map
      * box_handle_predicate_info map
    type maps =
        struct_info map
      * enum_info map
      * global_info map
      * inductive_info map
      * pure_func_info map
      * pred_ctor_info map
      * malloc_block_pred_info map
      * ((string * string) * field_pred_info) list
      * pred_fam_info map
      * pred_inst_map
      * type_ map (* typedefmap *)
      * func_type_info map
      * func_info map
      * box_info map
      * class_info map
      * interface_info map
      * termnode map (* classterms *)
      * termnode map (* interfaceterms *)
      * plugin_info map
    
    type implemented_prototype_info =
        string
      * loc
    type implemented_function_type_info =
        string (* function name *)
      * loc (* function location *)
      * string (* function type name *)
      * string list (* function type arguments; only module names are supported *)
      * bool (* function is declared in an unloadable module *)
    type check_file_output =
        implemented_prototype_info list
      * implemented_function_type_info list
  end in
  let open CheckFileTypes in
  
  (* Maps a header file name to the list of header file names that it includes, and the various maps of VeriFast elements that it declares directly. *)
  let headermap: ((loc * string) list * maps) map ref = ref [] in
  let spec_classes= ref [] in
  let spec_lemmas= ref [] in
  let meths_impl= ref [] in
  let cons_impl= ref [] in
  
  (** Verify the .c/.h/.jarsrc/.jarspec file whose headers are given by [headers] and which declares packages [ps].
      As a side-effect, adds all processed headers to the header map.
      Recursively calls itself on headers included by the current file.
      Returns the elements declared directly in the current file.
      May add symbols and global assumptions to the SMT solver.
      
      is_import_spec:
        true if the file being checked specifies a module used by the module being verified
        false if the file being checked specifies the module being verified
    *)
  let rec check_file (filepath: string) (is_import_spec : bool) (include_prelude : bool) (basedir : string) (headers : (loc * string) list) (ps : package list): check_file_output * maps =
  
  let is_jarspec = Filename.check_suffix filepath ".jarspec" in
  
  let
    (structmap0: struct_info map),
    (enummap0: enum_info map),
    (globalmap0: global_info map),
    (inductivemap0: inductive_info map),
    (purefuncmap0: pure_func_info map),
    (predctormap0: pred_ctor_info map),
    (malloc_block_pred_map0: malloc_block_pred_info map),
    (field_pred_map0: ((string * string) * field_pred_info) list),
    (predfammap0: pred_fam_info map),
    (predinstmap0: pred_inst_map),
    (typedefmap0: type_ map),
    (functypemap0: func_type_info map),
    (funcmap0: func_info map),
    (boxmap0: box_info map),
    (classmap0: class_info map),
    (interfmap0: interface_info map),
    (classterms0: termnode map),
    (interfaceterms0: termnode map),
    (pluginmap0: plugin_info map): maps =
  
    let append_nodups xys xys0 string_of_key l elementKind =
      let rec iter xys =
        match xys with
          [] -> xys0
        | ((x, y) as elem)::xys ->
          if List.mem_assoc x xys0 then static_error l ("Duplicate " ^ elementKind ^ " '" ^ string_of_key x ^ "'") None;
          elem::iter xys
      in
      iter xys
    in
    let id x = x in
    let merge_maps l
      (structmap, enummap, globalmap, inductivemap, purefuncmap, predctormap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, typedefmap, functypemap, funcmap, boxmap, classmap, interfmap, classterms, interfaceterms, pluginmap)
      (structmap0, enummap0, globalmap0, inductivemap0, purefuncmap0, predctormap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, typedefmap0, functypemap0, funcmap0, boxmap0, classmap0, interfmap0, classterms0, interfaceterms0, pluginmap0)
      =
      (append_nodups structmap structmap0 id l "struct",
       append_nodups enummap enummap0 id l "enum",
       append_nodups globalmap globalmap0 id l "global variable",
       append_nodups inductivemap inductivemap0 id l "inductive datatype",
       append_nodups purefuncmap purefuncmap0 id l "pure function",
       append_nodups predctormap predctormap0 id l "predicate constructor",
       malloc_block_pred_map @ malloc_block_pred_map0,
       field_pred_map @ field_pred_map0,
       append_nodups predfammap predfammap0 id l "predicate",
       append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance",
       append_nodups typedefmap typedefmap0 id l "typedef",
       append_nodups functypemap functypemap0 id l "function type",
       append_nodups funcmap funcmap0 id l "function",
       append_nodups boxmap boxmap0 id l "box predicate",
       append_nodups classmap classmap0 id l "class",
       append_nodups interfmap interfmap0 id l "interface",
       classterms @ classterms0, 
       interfaceterms @ interfaceterms0,
       if pluginmap0 <> [] && pluginmap <> [] then static_error l "VeriFast does not yet support loading multiple plugins" None else
       append_nodups pluginmap pluginmap0 id l "plugin")
    in

    (** [merge_header_maps maps0 headers] returns [maps0] plus all elements transitively declared in [headers]. *)
    let rec merge_header_maps include_prelude maps0 headers_included headers =
      match headers with
        [] -> (maps0, headers_included)
      | (l, header_path)::headers ->
        if List.mem header_path ["bool.h"; "assert.h"; "limits.h"] then
          merge_header_maps include_prelude maps0 headers_included headers
        else
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
                static_error l (Printf.sprintf "No such file: '%s'" localpath) None
          in
          if List.mem path headers_included then
            merge_header_maps include_prelude maps0 headers_included headers
          else
          begin
            let (headers', maps) =
              match try_assoc path !headermap with
                None ->
                let header_is_import_spec = Filename.chop_extension (Filename.basename header_path) <> Filename.chop_extension (Filename.basename program_path) in
                let (headers', ds) =
                  match language with
                    CLang ->
                    parse_header_file basedir relpath reportRange reportShouldFail
                  | Java ->
                    let (jars, javaspecs) = parse_jarspec_file_core path in
                    let ds = List.map (fun javaspec -> parse_java_file javaspec reportRange reportShouldFail) javaspecs in
                    if not header_is_import_spec then begin
                      let (classes, lemmas) = extract_specs ds in
                      spec_classes := classes;
                      spec_lemmas := lemmas
                    end;
                    let l = file_loc path in
                    let jarspecs = List.map (fun path -> (l, path ^ "spec")) jars in
                    (jarspecs, ds)
                in
                let (_, maps) = check_file header_path header_is_import_spec include_prelude basedir headers' ds in
                headermap := (path, (headers', maps))::!headermap;
                (headers', maps)
              | Some (headers', maps) ->
                (headers', maps)
            in
            let (maps0, headers_included) = merge_header_maps include_prelude maps0 headers_included headers' in
            merge_header_maps include_prelude (merge_maps l maps maps0) (path::headers_included) headers
          end
        end
    in

    let maps0 = ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []) in
    
    let (maps0, headers_included) =
      if include_prelude then
        match file_type path with
          | Java -> begin
            if rtpath = "nort" then (maps0, []) else
            match try_assoc rtpath !headermap with
              | None -> 
                let ([], javaspecs) = parse_jarspec_file_core rtpath in
                let javaspecs =
                  if options.option_allow_assume then Filename.concat rtdir "_assume.javaspec"::javaspecs else javaspecs
                in
                let ds = List.map (fun x -> parse_java_file x reportRange reportShouldFail) javaspecs in
                let (_, maps0) = check_file rtpath true false bindir [] ds in
                headermap := (rtpath, ([], maps0))::!headermap;
                (maps0, [])
              | Some ([], maps0) ->
                (maps0, [])
          end
          | CLang ->
            merge_header_maps false maps0 [] [(dummy_loc, "prelude.h")]
      else
        (maps0, [])
    in

    let (maps, _) = merge_header_maps include_prelude maps0 headers_included headers in
    maps
  in

  (* Region: structdeclmap, enumdeclmap, inductivedeclmap *)
  
  let pluginmap1 =
    ps |> List.fold_left begin fun pluginmap1 (PackageDecl (l, pn, ilist, ds)) ->
      ds |> List.fold_left begin fun pluginmap1 decl ->
        match decl with
          LoadPluginDecl (l, lx, x) ->
          if pluginmap0 <> [] || pluginmap1 <> [] then static_error l "VeriFast does not yet support loading multiple plugins" None;
          begin try
            let p = Plugins_private.load_plugin (Filename.concat basedir (x ^ "_verifast_plugin")) in
            let x = full_name pn x in
            (x, ((p, p#create_instance plugin_context), get_unique_var_symb x (PredType ([], [], None))))::pluginmap1
          with
            Plugins_private.LoadPluginError msg -> static_error l ("Could not load plugin: " ^ msg) None
          end
        | _ -> pluginmap1
      end pluginmap1
    end []
  in
  
  let pluginmap = pluginmap1 @ pluginmap0 in
  
  let unloadable =
    match language with
      | CLang ->
        let [PackageDecl (_, _, _, ds)] = ps in
        List.exists (function (UnloadableModuleDecl l) -> true | _ -> false) ds
      | Java -> false
  in
  
  let typedefdeclmap =
    let rec iter tddm ds =
      match ds with
        [] -> List.rev tddm
      | TypedefDecl (l, te, d)::ds ->
        (* C compiler detects duplicate typedefs *)
        iter ((d, (l, te))::tddm) ds
      | _::ds ->
        iter tddm ds
    in
    if language = Java then [] else
    let [PackageDecl(_,"",[],ds)] = ps in iter [] ds
  in
  
  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds_opt)::ds ->
        begin
          match try_assoc sn structmap0 with
            Some (_, Some _, _) -> static_error l "Duplicate struct name." None
          | Some (_, None, _) | None -> ()
        end;
        begin
          match try_assoc sn sdm with
            Some (_, Some _) -> static_error l "Duplicate struct name." None
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
        [] -> List.rev edm
      | EnumDecl(l, en, elems) :: ds ->
        begin 
          match try_assoc en edm with
        | Some((l', elems')) -> static_error l "Duplicate enum name." None
        | None -> iter ((en, (l, elems)) :: edm) ds
        end
      | _ :: ds -> iter edm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  in
  
  let enummap1 =
    let rec process_decls enummap1 ds =
      match ds with
        [] -> enummap1
      | (_, (l, elems))::ds ->
        let rec process_elems enummap1 nextValue elems =
          match elems with
            [] -> process_decls enummap1 ds
          | (c, expr_opt)::elems ->
            let value =
              match expr_opt with
                None -> nextValue
              | Some e ->
                let rec eval e =
                  match e with
                    IntLit (_, n, _) -> n
                  | Var (l, x, _) ->
                    begin match try_assoc2 x enummap1 enummap0 with
                      None -> static_error l "No such enumeration constant" None
                    | Some n -> n
                    end
                  | Operation (l, op, [e1; e2], _) ->
                    let n1 = eval e1 in
                    let n2 = eval e2 in
                    begin match op with
                      Add -> add_big_int n1 n2
                    | Sub -> sub_big_int n1 n2
                    | Mul -> mult_big_int n1 n2
                    | Div -> div_big_int n1 n2
                    | _ -> static_error l "This operation is not supported in this position." None
                    end
                  | e -> static_error (expr_loc e) "This expression form is not supported in this position." None
                in
                eval e
            in
            process_elems ((c, value)::enummap1) (succ_big_int value) elems
        in
        process_elems enummap1 zero_big_int elems
    in
    process_decls [] enumdeclmap
  in
  
  let functypenames = 
    let ds=match ps with
        [PackageDecl(_,"",[],ds)] -> ds
      | _ when file_type path=Java -> []
    in
    flatmap (function (FuncTypeDecl (l, gh, _, g, tps, ftps, _, _)) -> [g, (l, gh, tps, ftps)] | _ -> []) ds
  in
  
  let inductivedeclmap=
    let rec iter pn idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, tparams, ctors))::ds -> let n=full_name pn i in
        if n = "bool" || n = "boolean" || n = "int" || List.mem_assoc n idm || List.mem_assoc n inductivemap0 then
          static_error l "Duplicate datatype name." None
        else
          iter pn ((n, (l, tparams, ctors))::idm) ds
      | _::ds -> iter pn idm ds
    in
    let rec iter' idm ps=
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter pn idm ds) rest
      | [] -> List.rev idm
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
            static_error l ("Ambiguous imports for name '" ^ name ^ "': " ^ String.concat ", " fqns ^ ".") None
  in
  
  let search2' x (pn,imports) xys1 xys2 =
    match search' x (pn,imports) xys1 with
      None -> search' x (pn,imports) xys2
    | result -> result
  in
  
  (* Region: interfdeclmap, classmap1 *)
  
  let (interfmap1,classmap1)=
    let rec iter (pn,il) ifdm classlist ds =
      match ds with
        [] -> (ifdm, classlist)
      | (Interface (l, i, interfs, fields, meths, pred_specs))::ds -> let i= full_name pn i in 
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          let interfs =
            let rec check_interfs ls=
                match ls with
                  [] -> []
                | i::ls -> match search2' i (pn,il) ifdm interfmap0 with 
                            Some i -> i::check_interfs ls
                          | None -> static_error l ("Interface wasn't found: " ^ i) None
            in
            check_interfs interfs
          in
          iter (pn, il) ((i, (l, fields, meths, pred_specs, interfs, pn, il))::ifdm) classlist ds
      | (Class (l, abstract, fin, i, meths,fields,constr,super,interfs,preds))::ds -> 
        let i= full_name pn i in
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          let interfs =
            let rec check_interfs ls=
                match ls with
                  [] -> []
                | i::ls -> match search2' i (pn,il) ifdm interfmap0 with 
                            Some i -> i::check_interfs ls
                          | None -> static_error l ("Interface wasn't found: "^i) None
            in
            check_interfs interfs
          in
          let super =
            if i = "java.lang.Object" then "" else
            match search2' super (pn,il) classlist classmap0 with
              None-> static_error l ("Superclass wasn't found: "^super) None
            | Some super -> super
          in
          iter (pn,il) ifdm ((i, (l,abstract,fin,meths,fields,constr,super,interfs,preds,pn,il))::classlist) ds
      | _::ds -> iter (pn,il) ifdm classlist ds
    in
    let rec iter' (ifdm,classlist) ps =
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter (pn,ilist) ifdm classlist ds) rest
      | [] -> (List.rev ifdm, List.rev classlist)
    in
    iter' ([],[]) ps
  in
  
  let inductive_arities =
    List.map (fun (i, (l, tparams, _)) -> (i, (l, List.length tparams))) inductivedeclmap
    @ List.map (fun (i, (l, tparams, _, _)) -> (i, (l, List.length tparams))) inductivemap0
  in
  
  (* Region: check_pure_type: checks validity of type expressions *)
  
  let check_pure_type_core typedefmap1 (pn,ilist) tpenv te =
    let rec check te =
    match te with
      ManifestTypeExpr (l, t) -> t
    | ArrayTypeExpr (l, t) -> 
        let tp = check t in
        ArrayType(tp)
    | StaticArrayTypeExpr (l, t, s) ->
        let tp = check t in
        StaticArrayType(tp, s)
    | IdentTypeExpr (l, None, id) ->
      if List.mem id tpenv then
        TypeParam id
      else
      begin
      match try_assoc2 id typedefmap0 typedefmap1 with
        Some t -> t
      | None ->
      match resolve (pn,ilist) l id inductive_arities with
        Some (s, (ld, n)) ->
        if n > 0 then static_error l "Missing type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (s, [])
      | None ->
        match (search2' id (pn,ilist) classmap1 classmap0) with
          Some s -> ObjType s
        | None -> match (search2' id (pn,ilist) interfmap1 interfmap0) with
                    Some s->ObjType s
                  | None ->
                    if List.mem_assoc id functypenames || List.mem_assoc id functypemap0 then
                      FuncType id
                    else
                      static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^pn^" "^id) None
      end
    | IdentTypeExpr (l, Some(pac), id) ->
      let full_name = pac ^ "." ^ id in
      begin match (search2' full_name (pn,ilist) classmap1 classmap0) with
          Some s -> ObjType s
        | None -> match (search2' full_name (pn,ilist) interfmap1 interfmap0) with
                    Some s->ObjType s
                  | None -> static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^ full_name) None
      end
    | ConstructedTypeExpr (l, id, targs) ->
      begin
      match resolve (pn,ilist) l id inductive_arities with
        Some (id, (ld, n)) ->
        if n <> List.length targs then static_error l "Incorrect number of type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (id, List.map check targs)
      | None -> static_error l "No such inductive datatype." None
      end
    | StructTypeExpr (l, sn) ->
      if not (List.mem_assoc sn structmap0 || List.mem_assoc sn structdeclmap) then
        static_error l "No such struct." None
      else
        StructType sn
    | PtrTypeExpr (l, te) -> PtrType (check te)
    | PredTypeExpr (l, tes, inputParamCount) -> PredType ([], List.map check tes, inputParamCount)
    | PureFuncTypeExpr (l, tes) ->
      let ts = List.map check tes in
      let rec iter ts =
        match ts with
          [t1; t2] -> PureFuncType (t1, t2)
        | t1::ts -> PureFuncType (t1, iter ts)
        | _ -> static_error l "A fixpoint function type requires at least two types: a domain type and a range type" None
      in
      iter ts
    in
    check te
  in
  
  let typedefmap1 =
    let rec iter tdm1 tdds =
      match tdds with
        [] -> tdm1
      | (d, (l, te))::tdds ->
        let t = check_pure_type_core tdm1 ("",[]) [] te in
        iter ((d,t)::tdm1) tdds
    in
    iter [] typedefdeclmap
  in
  
  let typedefmap = typedefmap1 @ typedefmap0 in
  
  let check_pure_type (pn,ilist) tpenv te = check_pure_type_core typedefmap1 (pn,ilist) tpenv te in
  
  let classmap1 =
    List.map
      begin fun (sn, (l,abstract,fin,meths,fds,constr,super,interfs,preds,pn,ilist)) ->
        let rec iter fmap fds =
          match fds with
            [] -> (sn, (l,abstract,fin,meths, List.rev fmap,constr,super,interfs,preds,pn,ilist))
          | Field (fl, fgh, t, f, fbinding, fvis, ffinal, finit)::fds ->
            if List.mem_assoc f fmap then static_error fl "Duplicate field name." None;
            iter ((f, {fl; fgh; ft=check_pure_type (pn,ilist) [] t; fvis; fbinding; ffinal; finit; fvalue=ref None})::fmap) fds
        in
        iter [] fds
      end
      classmap1
  in
  
  let rec instantiate_type tpenv t =
    if tpenv = [] then t else
    match t with
      TypeParam x -> List.assoc x tpenv
    | PtrType t -> PtrType (instantiate_type tpenv t)
    | InductiveType (i, targs) -> InductiveType (i, List.map (instantiate_type tpenv) targs)
    | PredType ([], pts, inputParamCount) -> PredType ([], List.map (instantiate_type tpenv) pts, inputParamCount)
    | PureFuncType (t1, t2) -> PureFuncType (instantiate_type tpenv t1, instantiate_type tpenv t2)
    | InferredType t ->
      begin match !t with
        None -> assert false
      | Some t -> instantiate_type tpenv t
      end
    | ArrayType t -> ArrayType (instantiate_type tpenv t)
    | _ -> t
  in
  
  let instantiate_types tpenv ts =
    if tpenv = [] then ts else List.map (instantiate_type tpenv) ts
  in
  
  let terms_of xys =
    xys |> List.map begin fun (x, _) ->
      let t = ctxt#mk_app (mk_symbol x [] ctxt#type_int Uninterp) [] in
      let serialNumber = !class_counter in
      class_counter := !class_counter + 1;
      ctxt#assume (ctxt#mk_eq (ctxt#mk_app class_serial_number [t]) (ctxt#mk_intlit serialNumber));
      (x, t)
    end
  in
  let classterms1 =  terms_of classmap1 in
  let interfaceterms1 = terms_of interfmap1 in

  let classterms = classterms1 @ classterms0 in
  let interfaceterms = interfaceterms1 @ interfaceterms0 in
  
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
                 Some (get_unique_var_symb ("struct_" ^ sn ^ "_padding") (PredType ([], [PtrType (StructType sn)], Some 1)))
              )
             )
           | Field (lf, gh, t, f, Instance, Public, final, init)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name." None
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
   
  let structmap = structmap1 @ structmap0 in
  
  let enummap = enummap1 @ enummap0 in
  
  let isfuncs = if file_type path=Java then [] else
    flatmap (fun (ftn, (_, gh, tparams, ftps)) ->
      match (gh, tparams, ftps) with
        (Real, [], []) ->
        let isfuncname = "is_" ^ ftn in
        let domain = [ProverInt] in
        let symb = mk_func_symbol isfuncname domain ProverBool Uninterp in
        [(isfuncname, (dummy_loc, [], Bool, [PtrType Void], symb))]
      | _ -> []
    ) functypenames
  in
  
  let rec is_subtype_of x y =
    x = y ||
    y = "java.lang.Object" ||
    match try_assoc x classmap1 with
      Some (_, _, _, _, _, _, super, interfaces, _, _, _) ->
      is_subtype_of super y || List.exists (fun itf -> is_subtype_of itf y) interfaces
    | None ->
      match try_assoc x classmap0 with
        Some {csuper=super; cinterfs=interfaces} ->
        is_subtype_of super y || List.exists (fun itf -> is_subtype_of itf y) interfaces
      | None -> begin match try_assoc x interfmap1 with
          Some (_, _, _, _, interfaces, _, _) -> List.exists (fun itf -> is_subtype_of itf y) interfaces
        | None -> begin match try_assoc x interfmap0 with
            Some (InterfaceInfo (_, _, _, _, interfaces)) -> List.exists (fun itf -> is_subtype_of itf y) interfaces
          | None -> false 
          end
        end
  in
  let is_subtype_of_ x y =
    match (x, y) with
      (ObjType x, ObjType y) -> is_subtype_of x y
    | _ -> false
  in
  let is_unchecked_exception_type tp = 
    match tp with
     ObjType cn -> (is_subtype_of cn "java.lang.RuntimeException") || (is_subtype_of cn "java.lang.Error")
    | _ -> false
  in

  (* Region: globaldeclmap *)
  
  let globaldeclmap =
    let rec iter gdm ds =
      match ds with
        [] -> gdm
      | Global(l, te, x, init) :: ds -> (* typecheck the rhs *)
        begin
          match try_assoc x globalmap0 with
            Some(_) -> static_error l "Duplicate global variable name." None
          | None -> ()
        end;
        begin
          match try_assoc x gdm with
            Some (_) -> static_error l "Duplicate global variable name." None
          | None -> 
            let tp = check_pure_type ("",[]) [] te in
            let global_symb = get_unique_var_symb x (PtrType tp) in
            iter ((x, (l, tp, global_symb, ref init)) :: gdm) ds
        end
      | _::ds -> iter gdm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  in

  let globalmap1 = globaldeclmap in
  let globalmap = globalmap1 @ globalmap0 in
 
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
      (InferredType t', InferredType t0') -> if t' == t0' then true else begin t0' := Some t1; true end
    | (t, InferredType t0) -> t0 := Some t; true
    | (InferredType t, t0) -> t := Some t0; true
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
      i1=i2 && List.for_all2 unify args1 args2
    | (ArrayType t1, ArrayType t2) -> unify t1 t2
    | (PtrType t1, PtrType t2) -> compatible_pointees t1 t2
    | (t1, t2) -> t1 = t2
  in
  
  let rec expect_type_core l msg t t0 =
    match (unfold_inferred_type t, unfold_inferred_type t0) with
      (ObjType "null", ObjType _) -> ()
    | (ObjType "null", ArrayType _) -> ()
    | (ArrayType _, ObjType "java.lang.Object") -> ()
    | (StaticArrayType _, PtrType _) -> ()
    | (UChar, IntType) -> ()
    | (UChar, ShortType) -> ()
    | (UChar, UShortType) -> ()
    | (UChar, UintPtrType) -> ()
    | (Char, IntType) -> ()
    | (Char, ShortType) -> ()
    | (UShortType, IntType) -> ()
    | (UShortType, UintPtrType) -> ()
    | (ShortType, IntType) -> ()
    | (ObjType x, ObjType y) when is_subtype_of x y -> ()
    | (PredType ([], ts, inputParamCount), PredType ([], ts0, inputParamCount0)) ->
      begin
        match zip ts ts0 with
          Some tpairs when List.for_all (fun (t, t0) -> unify t t0) tpairs && (inputParamCount0 = None || inputParamCount = inputParamCount0) -> ()
        | _ -> static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
      end
    | (PureFuncType (t1, t2), PureFuncType (t10, t20)) -> expect_type_core l msg t10 t1; expect_type_core l msg t2 t20
    | (InductiveType _, AnyType) -> ()
    | (InductiveType (i1, args1), InductiveType (i2, args2)) when i1 = i2 ->
      List.iter2 (expect_type_core l msg) args1 args2
    | _ -> if unify t t0 then () else static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
  in
  
  let expect_type l t t0 = expect_type_core l "" t t0 in
  
  let is_assignable_to t t0 =
    try expect_type dummy_loc t t0; true with StaticError (l, msg, url) -> false (* TODO: Consider eliminating this hack *)
  in
  
  let is_assignable_to_sign sign sign0 = for_all2 is_assignable_to sign sign0 in
  
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
        if List.mem x tparams0 then static_error l (Printf.sprintf "Type parameter '%s' hides existing type parameter '%s'." x x) None;
        if List.mem x xs then static_error l (Printf.sprintf "Duplicate type parameter '%s'." x) None;
        iter xs
    in
    iter tparams
  in
  
  let (inductivemap1, purefuncmap1, fixpointmap1) =
    let rec iter (pn,ilist) imap pfm fpm ds =
      match ds with
        [] -> (imap, pfm, fpm)
      | Inductive (l, i, tparams, ctors)::ds -> let i=full_name pn i in
        check_tparams l [] tparams;
        let rec citer j ctormap pfm ctors =
          match ctors with
            [] -> iter (pn,ilist) ((i, (l, tparams, List.rev ctormap))::imap) pfm fpm ds
          | Ctor (lc, cn, tes)::ctors ->
            let full_cn = full_name pn cn in
            if List.mem_assoc full_cn pfm || List.mem_assoc full_cn purefuncmap0 then
              static_error lc ("Duplicate pure function name: " ^ full_cn) None
            else (
              let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
              let csym =
                mk_func_symbol full_cn (List.map provertype_of_type ts) ProverInductive (Proverapi.Ctor (CtorByOrdinal j))
              in
              let purefunc = (full_cn, (lc, tparams, InductiveType (i, List.map (fun x -> TypeParam x) tparams), ts, csym)) in
              citer (j + 1) ((cn, purefunc)::ctormap) (purefunc::pfm) ctors
            )
        in
        citer 0 [] pfm ctors
      | Func (l, Fixpoint, tparams, rto, g, ps, nonghost_callers_only, functype, contract, body_opt,Static,Public)::ds ->
        let g = full_name pn g in
        if List.mem_assoc g pfm || List.mem_assoc g purefuncmap0 then static_error l ("Duplicate pure function name: "^g) None;
        check_tparams l [] tparams;
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void." None
          | Some rt -> (check_pure_type (pn,ilist) tparams rt)
        in
        if nonghost_callers_only then static_error l "A fixpoint function cannot be marked nonghost_callers_only." None;
        if functype <> None then static_error l "Fixpoint functions cannot implement a function type." None;
        if contract <> None then static_error l "Fixpoint functions cannot have a contract." None;
        let pmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, p)::ps ->
              let _ = if List.mem_assoc p pmap then static_error l "Duplicate parameter name." None in
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((p, t)::pmap) ps
          in
          iter [] ps
        in
        begin match body_opt with
          Some ([SwitchStmt (ls, e, cs) as body], _) ->
          let index = 
            match e with
              Var (lx, x, _) ->
              begin match try_assoc_i x pmap with
                None -> static_error lx "Fixpoint function must switch on a parameter." None
              | Some (index, _) -> index
              end
            | _ -> static_error l "Fixpoint function must switch on a parameter." None
          in
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) (Proverapi.Fixpoint index) in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, tparams, rt, pmap, Some index, body, pn, ilist, fst fsym))::fpm) ds
        | Some ([ReturnStmt (lr, Some e) as body], _) ->
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, tparams, rt, pmap, None, body, pn, ilist, fst fsym))::fpm) ds
        | None ->
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) fpm ds
        | _ -> static_error l "Body of fixpoint function must be switch statement or return statement." None
        end
      | _::ds -> iter (pn,ilist) imap pfm fpm ds
    in
    let rec iter' (imap,pfm,fpm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) imap pfm fpm ds) rest
      | [] -> (List.rev imap, List.rev pfm, List.rev fpm)
    in
    iter' ([],isfuncs,[]) ps
  in
  
  let () =
    let welldefined_map = List.map (fun (i, info) -> let ec = ref (`EqClass (0, [])) in let ptr = ref ec in ec := `EqClass (0, [ptr]); (i, (info, ptr))) inductivemap1 in
    let merge_ecs ec0 ec1 =
      let `EqClass (ecrank0, ecmems0) = !ec0 in
      let `EqClass (ecrank1, ecmems1) = !ec1 in
      if ecrank0 <> ecrank1 then begin
        assert (ecrank0 < ecrank1);
        List.iter (fun ptr -> ptr := ec0) ecmems1;
        ec0 := `EqClass (ecrank0, ecmems1 @ ecmems0)
      end
    in
    let rec check_welldefined rank negative_rank pred_ptrs (i, ((l, _, ctors), ptr)) =
      (* Invariant:
         - All nodes reachable from a -1 node are -1
         - There are no cycles through -1 nodes that go through a negative occurrence.
         - The ranks of all nodes are less than the current rank [rank]
         - There are no cycles that go through a negative occurrence in the subgraph that is to the left of the current path.
         - All nodes reachable from a given node in the subgraph that is to the left of the current path, have either the same rank, a higher rank, or rank -1, but never rank 0
         - For any two nodes in the subgraph that is to the left of the current path, they are mutually reachable iff they are in the same equivalence class (and consequently have the same rank)
         - The ranks of the nodes on the current path are always (non-strictly) increasing
       *)
      let pred_ptrs = ptr::pred_ptrs in
      let ec = !ptr in
      let `EqClass (ecrank, ecmems) = !ec in
      if ecrank = -1 then
        ()
      else
      begin
        assert (ecrank = 0 && match ecmems with [ptr'] when ptr' == ptr -> true | _ -> false);
        ec := `EqClass (rank, ecmems);
        let rec check_ctor (ctorname, (_, (_, _, _, pts, _))) =
          let rec check_type negative pt =
            match pt with
              Bool | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> ()
            | TypeParam _ -> if negative then static_error l "A type parameter may not appear in a negative position in an inductive datatype definition." None
            | InductiveType (i0, tps) ->
              List.iter (fun t -> check_type negative t) tps;
              begin match try_assoc i0 welldefined_map with
                None -> ()
              | Some (info0, ptr0) ->
                let ec0 = !ptr0 in
                let `EqClass (ecrank0, ecmems0) = !ec0 in
                let negative_rank = if negative then rank else negative_rank in
                if ecrank0 > 0 then begin
                  if ecrank0 <= negative_rank then static_error l "This inductive datatype is not well-defined; it occurs recursively in a negative position." None;
                  let rec merge_preds pred_ptrs =
                    match pred_ptrs with
                      [] -> ()
                    | ptr1::pred_ptrs ->
                      let ec1 = !ptr1 in
                      let `EqClass (ecrank1, ecmems1) = !ec1 in
                      if ecrank0 < ecrank1 then begin
                        merge_ecs ec0 ec1;
                        merge_preds pred_ptrs
                      end
                  in
                  merge_preds pred_ptrs
                end else
                  check_welldefined (rank + 1) negative_rank pred_ptrs (i0, (info0, ptr0))
              end
            | PredType (tps, pts, _) ->
              assert (tps = []);
              List.iter (fun t -> check_type true t) pts
            | PureFuncType (t1, t2) ->
              check_type true t1; check_type negative t2
          in
          List.iter (check_type false) pts
        in
        List.iter check_ctor ctors;
        (* If this node is the leader of an equivalence class, then this equivalence class has now been proven to be well-defined. *)
        let ec = !ptr in
        let `EqClass (ecrank, ecmems) = !ec in
        if ecrank = rank then
          ec := `EqClass (-1, ecmems)
      end
    in
    List.iter (check_welldefined 1 0 []) welldefined_map
    (* Postcondition: there are no cycles in the inductive datatype definition graph that go through a negative occurrence. *)
  in
  
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
            [] -> static_error l "Inductive datatype is not inhabited." None
          | (_, (_, (_, _, _, pts, _)))::ctors ->
            let rec type_is_inhabited tp =
              match tp with
                Bool | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> true
              | TypeParam _ -> true  (* Should be checked at instantiation site. *)
              | PredType (tps, pts, _) -> true
              | PureFuncType (t1, t2) -> type_is_inhabited t2
              | InductiveType (i0, tps) ->
                List.for_all type_is_inhabited tps &&
                begin match try_assoc i0 inhabited_map with
                  None -> true
                | Some ((l0, _, ctors0), status0) ->
                  !status0 <> 1 &&
                  (check_inhabited i0 l0 ctors0 status0; true)
                end
            in
            if List.for_all type_is_inhabited pts then () else find_ctor ctors
        in
        find_ctor ctors;
        status := 2
      end
    in
    List.iter (fun (i, ((l, _, ctors), status)) -> check_inhabited i l ctors status) inhabited_map
  in
  
  let inductivemap1 =
    let infinite_map = List.map (fun (i, info) -> let status = ref (0, []) in (i, (info, status))) inductivemap1 in
    (* Status: (n, tparams) with n: 0 = not visited; 1 = currently visiting; 2 = infinite if one of tparams is infinite; 3 = unconditionally infinite *)
    (* Infinite = has infinitely many values *)
    let rec determine_type_is_infinite (i, ((l, tparams, ctors), status)) =
      let (n, _) = !status in
      if n < 2 then begin
        status := (1, []);
        let rec fold_cond cond f xs =
          match xs with
            [] -> Some cond
          | x::xs ->
            begin match f x with
              None -> None
            | Some cond' -> fold_cond (cond' @ cond) f xs
            end
        in
        let ctor_is_infinite (cn, (_, (lc, _, _, pts, _))) =
          let rec type_is_infinite tp =
            match tp with
              Bool -> Some []
            | TypeParam x -> Some [x]
            | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | PredType (_, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> None
            | PureFuncType (_, _) -> None (* CAVEAT: This assumes we do *not* have extensionality *)
            | InductiveType (i0, targs) ->
              begin match try_assoc i0 infinite_map with
                Some (info0, status0) ->
                let (n, cond) = !status0 in
                if n = 1 then
                  None
                else begin
                  if n = 0 then determine_type_is_infinite (i0, (info0, status0));
                  let (n, cond) = !status0 in
                  if n = 3 then None else
                  let (_, tparams, _) = info0 in
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              | None ->
                let (_, tparams, _, cond) = List.assoc i0 inductivemap0 in
                begin match cond with
                  None -> None
                | Some cond ->
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              end
          in
          fold_cond [] type_is_infinite pts
        in
        match fold_cond [] ctor_is_infinite ctors with
          None -> status := (3, [])
        | Some cond -> status := (2, cond)
      end
    in
    List.iter determine_type_is_infinite infinite_map;
    infinite_map |> List.map
      begin fun (i, ((l, tparams, ctors), status)) ->
        let (n, cond) = !status in
        let cond = if n = 2 then Some cond else None in
        (i, (l, tparams, ctors, cond))
      end
  in
  
  let inductivemap = inductivemap1 @ inductivemap0 in
  
  (* A universal type is one that is isomorphic to the universe for purposes of type erasure *)
  let rec is_universal_type tp =
    match tp with
      Bool -> false
    | TypeParam x -> true
    | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | PredType (_, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> true
    | PureFuncType (t1, t2) -> is_universal_type t1 && is_universal_type t2
    | InductiveType (i0, targs) ->
      let (_, _, _, cond) = List.assoc i0 inductivemap in
      cond <> Some [] && List.for_all is_universal_type targs
  in
  
  let functypedeclmap1 =
    let rec iter (pn,ilist) functypedeclmap1 ds =
      match ds with
        [] -> functypedeclmap1
      | FuncTypeDecl (l, gh, rt, ftn, tparams, ftxs, xs, (pre, post))::ds ->
        let ftn0 = ftn in
        let ftn = full_name pn ftn in
        if gh = Real && tparams <> [] then static_error l "Declaring type parameters on non-lemma function types is not supported." None;
        let _ = if List.mem_assoc ftn functypedeclmap1 || List.mem_assoc ftn functypemap0 then static_error l "Duplicate function type name." None in
        let rec check_tparams_distinct tparams =
          match tparams with
            [] -> ()
          | x::xs ->
            if List.mem x xs then static_error l "Duplicate type parameter" None;
            check_tparams_distinct xs
        in
        check_tparams_distinct tparams;
        (* The return type cannot mention type parameters. *)
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
        let ftxmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate function type parameter name." None;
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((x, t)::xm) xs
          in
          iter [] ftxs
        in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm || List.mem_assoc x ftxmap then static_error l "Duplicate parameter name." None;
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        iter (pn,ilist) ((ftn, (l, gh, tparams, rt, ftxmap, xmap, ftn0, pn, ilist, pre, post))::functypedeclmap1) ds
      | _::ds -> iter (pn,ilist) functypedeclmap1 ds
    in
    let rec iter' functypedeclmap1 ps =
      match ps with
        [] -> List.rev functypedeclmap1
      | PackageDecl (_, pn, ilist, ds)::ps -> iter' (iter (pn,ilist) functypedeclmap1 ds) ps
    in
    iter' [] ps
  in
  
  (* Region: predicate families *)
  
  let mk_predfam p l tparams arity ts inputParamCount = (p, (l, tparams, arity, ts, get_unique_var_symb p (PredType (tparams, ts, inputParamCount)), inputParamCount)) in

  let struct_padding_predfams1 =
    flatmap
      (function
         (sn, (l, fds, Some padding_predsymb)) -> [("struct_" ^ sn ^ "_padding", (l, [], 0, [PtrType (StructType sn)], padding_predsymb, Some 1))]
       | _ -> [])
      structmap1
  in
  
  let functypedeclmap1 =
    List.map
      begin fun (g, (l, gh, tparams, rt, ftxmap, xmap, g0, pn, ilist, pre, post)) ->
        let predfammaps =
          if gh = Ghost || ftxmap <> [] then
            let paramtypes = [PtrType (FuncType g)] @ List.map snd ftxmap in
            [mk_predfam (full_name pn ("is_" ^ g0)) l tparams 0 paramtypes (Some (List.length paramtypes))]
          else
            []
        in
        (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, predfammaps))
      end
      functypedeclmap1
  in
  
  let isparamizedfunctypepreds1 = flatmap (fun (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, predfammaps)) -> predfammaps) functypedeclmap1 in
  
  let malloc_block_pred_map1 = 
    structmap1 |> flatmap begin function
      (sn, (l, Some _, _)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) l [] 0 [PtrType (StructType sn)] (Some 1))]
    | _ -> []
    end
  in
  
  let malloc_block_pred_map = malloc_block_pred_map1 @ malloc_block_pred_map0 in

  let field_pred_map1 = (* dient om dingen te controleren bij read/write controle v velden*)
    match file_type path with
      Java ->
      classmap1 |> flatmap begin fun (cn, (_,_,_,_, fds,_,_,_,_,_,_)) ->
        fds |> List.map begin fun (fn, {fl; ft; fbinding}) ->
          let predfam =
            match fbinding with
              Static -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ft] (Some 0)
            | Instance -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ObjType cn; ft] (Some 1)
          in
          ((cn, fn), predfam)
        end
      end
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
                None -> static_error l "Predicate family redeclarations declares a different number of type parameters." None
              | Some bs -> bs
            in
            let ts0' = List.map (instantiate_type tpenv) ts0 in
            if arity <> arity0 || ts <> ts0' || inputParamCount <> inputParamCount0 then
              static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.") None;
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
    iter' (isparamizedfunctypepreds1 @ structpreds1) ps
  in
  
  let (boxmap, predfammap1) =
    let rec iter (pn,ilist) bm pfm ds =
      match ds with
        [] -> (bm, pfm)
      | BoxClassDecl (l, bcn, ps, inv, ads, hpds)::ds -> let bcn= full_name pn bcn in
        if List.mem_assoc bcn pfm || List.mem_assoc bcn purefuncmap0 then static_error l "Box class name clashes with existing predicate name." None;
        let default_hpn = bcn ^ "_handle" in
        if List.mem_assoc default_hpn pfm then static_error l ("Default handle predicate name '" ^ default_hpn ^ "' clashes with existing predicate name.") None;
        let boxpmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
              if startswith x "old_" then static_error l "Box parameter name cannot start with old_." None;
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
              if List.mem_assoc an amap then static_error l "Duplicate action name." None;
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Action parameter clashes with box parameter." None;
                    if List.mem_assoc x pmap then static_error l "Duplicate action parameter name." None;
                    if startswith x "old_" then static_error l "Action parameter name cannot start with old_." None;
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
              if List.mem_assoc hpn hpm then static_error l "Duplicate handle predicate name." None;
              if List.mem_assoc hpn pfm then static_error l "Handle predicate name clashes with existing predicate name." None;
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Handle predicate parameter clashes with box parameter." None;
                    if List.mem_assoc x pmap then static_error l "Duplicate handle predicate parameter name." None;
                    if startswith x "old_" then static_error l "Handle predicate parameter name cannot start with old_." None;
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
  
  let interfmap1 =
    let rec iter_interfs interfmap1_done interfmap1_todo =
      match interfmap1_todo with
        [] -> List.rev interfmap1_done
      | (tn, (li, fields, methods, preds, interfs, pn, ilist))::interfmap1_todo ->
        let rec iter_preds predmap preds =
          match preds with
            [] -> iter_interfs ((tn, (li, fields, methods, List.rev predmap, interfs, pn, ilist))::interfmap1_done) interfmap1_todo
          | InstancePredDecl (l, g, ps, body)::preds ->
            if List.mem_assoc g predmap then static_error l "Duplicate predicate name." None;
            let pmap =
              let rec iter pmap ps =
                match ps with
                  [] -> List.rev pmap
                | (tp, x)::ps ->
                  if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
                  let tp = check_pure_type (pn,ilist) [] tp in
                  iter ((x, tp)::pmap) ps
              in
              iter [] ps
            in
            let (family, symb) =
              let rec preds_in_itf tn =
                let check_itfmap get_preds_and_itfs itfmap fallback =
                  begin match try_assoc tn itfmap with
                    Some info ->
                    let (preds, itfs) = get_preds_and_itfs info in
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfs
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist) -> (preds, interfs)) interfmap1_done $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              match flatmap preds_in_itf interfs with
                [] -> (tn, get_unique_var_symb (tn ^ "#" ^ g) (PredType ([], [], None)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" t t0; true) pmap pmap0) then
                  static_error l "Predicate override check: parameter count mismatch" None;
                (family, symb)
              | _ -> static_error l "Ambiguous override: multiple overridden predicates" None
            in
            iter_preds ((g, (l, pmap, family, symb))::predmap) preds
        in
        iter_preds [] preds
    in
    iter_interfs [] interfmap1
  in
  
  let classmap1 =
    let rec iter classmap1_done classmap1_todo =
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist))::classmap1_todo ->
        let cont predmap = iter ((cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, List.rev predmap, pn, ilist))::classmap1_done) classmap1_todo in
        let rec iter predmap preds =
          match preds with
            [] -> cont predmap
          | InstancePredDecl (l, g, ps, body)::preds ->
            if List.mem_assoc g predmap then static_error l "Duplicate predicate name." None;
            let pmap =
              let rec iter pmap ps =
                match ps with
                  [] -> List.rev pmap
                | (tp, x)::ps ->
                  if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
                  let tp = check_pure_type (pn,ilist) [] tp in
                  iter ((x, tp)::pmap) ps
              in
              iter [] ps
            in
            let (family, symb) =
              let rec preds_in_itf tn =
                let check_itfmap get_preds_and_itfs itfmap fallback =
                  begin match try_assoc tn itfmap with
                    Some info ->
                    let (preds, itfs) = get_preds_and_itfs info in
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfs
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist) -> (preds, interfs)) interfmap1 $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              let rec preds_in_class cn =
                if cn = "" then [] else
                let check_classmap classmap proj fallback =
                  begin match try_assoc cn classmap with
                    Some info ->
                    let (super, interfs, predmap) = proj info in
                    begin match try_assoc g predmap with
                      Some (l, pmap, family, symb, body) -> [(family, pmap, symb)]
                    | None -> preds_in_class super @ flatmap preds_in_itf interfs
                    end
                  | None -> fallback ()
                  end
                in
                check_classmap classmap1_done
                  (function (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, predmap, pn, ilist) -> (super, interfs, predmap))
                  $. fun () ->
                check_classmap classmap0
                  (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
                  $. fun () ->
                []
              in
              match preds_in_class super @ flatmap preds_in_itf interfs with
                [] -> (cn, get_unique_var_symb (cn ^ "#" ^ g) (PredType ([], [], None)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" t t0; true) pmap pmap0) then
                  static_error l "Predicate override check: parameter count mismatch" None;
                (family, symb)
              | _ -> static_error l "Ambiguous override: multiple overridden predicates" None
            in
            iter ((g, (l, pmap, family, symb, body))::predmap) preds
        in
        iter [] preds
    in
    iter [] classmap1
  in
  
  let (predctormap1, purefuncmap1) =
    let rec iter (pn,ilist) pcm pfm ds =
      match ds with
        PredCtorDecl (l, p, ps1, ps2, body)::ds -> let p=full_name pn p in
        begin
          match try_assoc2' (pn,ilist) p pfm purefuncmap0 with
            Some _ -> static_error l "Predicate constructor name clashes with existing pure function name." None
          | None -> ()
        end;
        begin
          match try_assoc' (pn,ilist) p predfammap with
            Some _ -> static_error l "Predicate constructor name clashes with existing predicate or predicate familiy name." None
          | None -> ()
        end;
        let ps1 =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              begin
                match try_assoc x pmap with
                  Some _ -> static_error l "Duplicate parameter name." None
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
                  Some _ -> static_error l "Duplicate parameter name." None
                | _ -> ()
              end;
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::psmap) ((x, t)::pmap) ps
          in
          iter ps1 [] ps2
        in
        let funcsym = mk_func_symbol p (List.map (fun (x, t) -> provertype_of_type t) ps1) ProverInductive Proverapi.Uninterp in
        let pf = (p, (l, [], PredType ([], List.map (fun (x, t) -> t) ps2, None), List.map (fun (x, t) -> t) ps1, funcsym)) in
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
  
  (* Region: The type checker *)
  
  let funcnames =
    list_remove_dups
      begin flatmap
        begin fun (PackageDecl (_, pn, _, ds)) ->
          flatmap
            begin function
              (Func (l, (Regular|Lemma(_)), tparams, rt, g, ps, nonghost_callers_only, ft, c, b,Static,Public)) -> [full_name pn g]
            | _ -> []
            end
            ds
        end
        ps
      end
  in
  
  let check_classname (pn, ilist) (l, c) =
    match resolve (pn, ilist) l c classmap1 with 
      None -> static_error l "No such class name." None
    | Some (s, _) -> s
  in
  
  let check_classnamelist (pn,ilist) is =
    List.map (check_classname (pn, ilist)) is
  in
  
  let check_funcnamelist is =
    List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such function name." None; i) is 
  in
  
  let interfmap1 =
    interfmap1 |> List.map begin function (i, (l, fields, meths, preds, supers, pn, ilist)) ->
      let fieldmap =
        fields |> List.map begin function Field (fl, fgh, ft, f, _, _, _, finit) ->
          let ft = check_pure_type (pn,ilist) [] ft in
          (f, {fl; fgh; ft; fvis=Public; fbinding=Static; ffinal=true; finit; fvalue=ref None})
        end
      in
      (i, (l, fieldmap, meths, preds, supers, pn, ilist))
    end
  in
  
  let rec lookup_class_field cn fn =
    match try_assoc cn classmap1 with
      Some (_, _, _, _, fds, _, super, itfs, _, _, _) ->
      begin match try_assoc fn fds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (f, cn)
      | None ->
      match lookup_class_field super fn with
        Some _ as result -> result
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) itfs
      end
    | None -> 
    match try_assoc cn classmap0 with
      Some {cfds; csuper; cinterfs} ->
      begin match try_assoc fn cfds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (f, cn)
      | None ->
      match lookup_class_field csuper fn with
        Some _ as result -> result
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) cinterfs
      end
    | None ->
    match try_assoc cn interfmap1 with
      Some (_, fds, _, _, supers, _, _) ->
      begin match try_assoc fn fds with
        Some f -> Some (f, cn)
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) supers
      end
    | None ->
    match try_assoc cn interfmap0 with
      Some (InterfaceInfo (_, fds, _, _, supers)) ->
      begin match try_assoc fn fds with
        Some f -> Some (f, cn)
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) supers
      end
    | None ->
    None
  in

  let is_package x =
    let x = x ^ "." in
    let has_package map = List.exists (fun (cn, _) -> startswith cn x) map in
    has_package classmap1 || has_package classmap0 || has_package interfmap1 || has_package interfmap0
  in
  
  let current_class = "#currentClass" in
  
  let rec check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e: (expr (* typechecked expression *) * type_ (* expression type *) * big_int option (* constant integer expression => value*)) =
    let check e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    let checkt e t0 = check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 false in
    let checkt_cast e t0 = 
      (*if (file_type path = Java) then
        let (w, et) = check e in
        (match (t0, et) with
          ((Char | ShortType | IntType), (Char | ShortType | IntType)) -> w
        | (ObjType "object", (ObjType (_) | ArrayType(_))) -> w (* stupid-cast *)
        | ((ObjType (_) | ArrayType(_)), ObjType "object") -> w
        | (ObjType(_), ObjType(_)) -> w
        | _ -> static_error (expr_loc e) (sprintf "illegal cast to %s from %s" (string_of_type t0) (string_of_type et)))
      else *)
        check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 true in
    let rec get_methods tn mn =
      if tn = "" then [] else
      match try_assoc tn classmap with
        Some {cmeths; csuper; cinterfs} ->
        let inherited_methods =
          get_methods csuper mn @ flatmap (fun ifn -> get_methods ifn mn) cinterfs
        in
        let declared_methods =
          flatmap
            begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract)) ->
              if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre_dyn, post_dyn, epost_dyn, fb, v, abstract))] else []
            end
            cmeths
        in
        declared_methods @ List.filter (fun (sign, info) -> not (List.mem_assoc sign declared_methods)) inherited_methods
      | None ->
      let InterfaceInfo (_, fields, meths, _, interfs) = List.assoc tn interfmap in
      let declared_methods = flatmap
        begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, v, abstract)) ->
          if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre, post, epost, Instance, v, abstract))] else []
        end
        meths
      in
      let inherited_methods = flatmap (fun ifn -> get_methods ifn mn) interfs in
      declared_methods @ List.filter (fun (sign, info) -> not (List.mem_assoc sign declared_methods)) inherited_methods
    in
    let promote_numeric e1 e2 ts =
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      match (unfold_inferred_type t1, unfold_inferred_type t2) with
        (IntType, RealType) ->
        let w1 = checkt e1 RealType in
        ts := Some [RealType; RealType];
        (w1, w2, RealType)
      | (RealType, IntType) ->
        let w2 = checkt e2 RealType in
        ts := Some [RealType; RealType];
        (w1, w2, RealType)
      | ((Char|ShortType|IntType), (Char|ShortType|IntType)) ->
        ts := Some [IntType; IntType];
        (w1, w2, IntType)
      | (t1, t2) ->
        let w2 = checkt e2 t1 in
        ts := Some [t1; t1];
        (w1, w2, t1)
    in
    let promote l e1 e2 ts =
      match promote_numeric e1 e2 ts with
        (w1, w2, (Char | ShortType | IntType | RealType | UintPtrType | PtrType _)) as result -> result
      | _ -> static_error l "Expression of type char, short, int, real, or pointer type expected." None
    in
    let check_pure_fun_value_call l w t es =
      if es = [] then static_error l "Zero-argument application of pure function value makes no sense." None;
      let box e t = convert_provertype_expr e (provertype_of_type t) ProverInductive in
      let unbox e t = convert_provertype_expr e ProverInductive (provertype_of_type t) in
      let (ws, tp) =
        let rec apply ws t es =
          match (es, t) with
            ([], t) -> (List.rev ws, t)
          | (e::es, PureFuncType (t1, t2)) -> apply (box (checkt e t1) t1::ws) t2 es
          | (e::es, _) -> static_error l "Too many arguments" None
        in
        apply [] t es
      in
      (unbox (WPureFunValueCall (l, w, ws)) tp, tp, None)
    in
    match e with
      True l -> (e, boolt, None)
    | False l -> (e, boolt, None)
    | Null l -> (e, ObjType "null", None)
    | Var (l, x, scope) ->
      begin
      match try_assoc x tenv with
      | Some(RefType(t)) -> scope := Some LocalVar; (Deref(l, e, ref (Some t)), t, None)
      | Some t -> scope := Some LocalVar; (e, t, None)
      | None ->
      begin fun cont ->
      if language <> Java then cont () else
      let field_of_this =
        match try_assoc "this" tenv with
        | Some ObjType cn ->
          begin match lookup_class_field cn x with
            None -> None
          | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
            let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
            in
            Some (WRead (l, Var (l, "this", ref (Some LocalVar)), fclass, x, ft, fbinding = Static, fvalue, fgh), ft, constant_value)
          end
        | _ -> None
      in
      match field_of_this with
        Some result -> result
      | None ->
      let field_of_class =
        match try_assoc current_class tenv with
          None -> None
        | Some (ClassOrInterfaceName cn) ->
          match lookup_class_field cn x with
            None -> None
          | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
            if fbinding <> Static then static_error l "Instance field access without target object" None;
            let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
            in
            Some (WRead (l, Var (l, current_class, ref (Some LocalVar)), fclass, x, ft, true, fvalue, fgh), ft, constant_value)
      in
      match field_of_class with
        Some result -> result
      | None ->
      match resolve (pn,ilist) l x classmap1 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x interfmap1 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x classmap0 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x interfmap0 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      if is_package x then
        (e, PackageName x, None)
      else
        cont ()
      end $. fun () ->
      match resolve (pn,ilist) l x purefuncmap with
      | Some (x, (_, tparams, t, [], _)) ->
        if tparams <> [] then
        begin
          let targs = List.map (fun _ -> InferredType (ref None)) tparams in
          let Some tpenv = zip tparams targs in
          scope := Some PureCtor;
          (Var (l, x, scope), instantiate_type tpenv t, None)
        end
        else
        begin
          scope := Some PureCtor; (Var (l, x, scope), t, None)
        end
      | _ ->
      if List.mem x funcnames then
        match file_type path with
          Java -> static_error l "In java methods can't be used as pointers" None
        | _ -> scope := Some FuncName; (e, PtrType Void, None)
      else
      match resolve (pn,ilist) l x predfammap with
      | Some (x, (_, tparams, arity, ts, _, inputParamCount)) ->
        if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
        if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
        scope := Some PredFamName;
        (Var (l, x, scope), PredType (tparams, ts, inputParamCount), None)
      | None ->
      match try_assoc x enummap with
      | Some i ->
        scope := Some (EnumElemName i);
        (e, IntType, None)
      | None ->
      match try_assoc' (pn, ilist) x globalmap with
      | Some ((l, tp, symbol, init)) -> scope := Some GlobalName; (e, tp, None)
      | None ->
      match try_assoc x modulemap with
      | Some _ when language <> Java -> scope := Some ModuleName; (e, IntType, None)
      | _ ->
      match resolve (pn,ilist) l x purefuncmap with
        Some (x, (_, tparams, t, pts, _)) ->
        let (pts, t) =
          if tparams = [] then
            (pts, t)
          else
            let tpenv = List.map (fun x -> (x, InferredType (ref None))) tparams in
            (List.map (instantiate_type tpenv) pts, instantiate_type tpenv t)
        in
        scope := Some PureFuncName; (Var (l, x, scope), List.fold_right (fun t1 t2 -> PureFuncType (t1, t2)) pts t, None)
      | None ->
      if language = Java then
        static_error l "No such variable, field, class, interface, package, inductive datatype constructor, or predicate" None
      else
        static_error l ("No such variable, constructor, regular function, predicate, enum element, global variable, or module: " ^ x) None
      end
    | PredNameExpr (l, g) ->
      begin
        match resolve (pn,ilist) l g predfammap with
          Some (g, (_, tparams, arity, ts, _, inputParamCount)) ->
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
          if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
          (PredNameExpr (l, g), PredType (tparams, ts, inputParamCount), None)
        | None -> static_error l "No such predicate." None
      end
    | Operation (l, (Eq | Neq as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote_numeric e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, (Or | And as operator), [e1; e2], ts) -> 
      let w1 = checkt e1 boolt in
      let w2 = checkt e2 boolt in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, Not, [e], ts) -> 
      let w = checkt e boolt in
      (Operation (l, Not, [w], ts), boolt, None)
    | Operation (l, BitAnd, [e1; e2], ts) ->
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      begin match (t1, t2) with
        ((Char|ShortType|IntType|UintPtrType), (Char|ShortType|IntType|UintPtrType)) ->
        let t = match (t1, t2) with (UintPtrType, _) | (_, UintPtrType) -> UintPtrType | _ -> IntType in
        ts := Some [t1; t2];
        (Operation (l, BitAnd, [w1; w2], ts), t, None)
      | _ -> static_error l "Arguments to bitwise operators must be integral types." None
      end
    | Operation (l, (BitXor | BitOr as operator), [e1; e2], ts) ->
      let (w1, t1, _) = check e1 in
      let (_, t2, _) = check e2 in
      begin
      match t1 with
        (Char | ShortType | IntType) -> let w2 = checkt e2 IntType in ts := Some [t1;t2]; (Operation (l, operator, [w1; w2], ts), IntType, None)
      | UintPtrType -> let w2 = checkt e2 UintPtrType in (Operation (l, operator, [w1; w2], ts), UintPtrType, None)
      | _ -> static_error l "Arguments to bitwise operators must be integral types." None
      end
    | Operation (l, Mod, [e1; e2], ts) ->
      let w1 = checkt e1 IntType in
      let w2 = checkt e2 IntType in
      (Operation (l, Mod, [w1; w2], ts), IntType, None)
    | Operation (l, BitNot, [e], ts) ->
      let (w, t, _) = check e in
      begin
      match t with
        Char | ShortType | IntType -> ts := Some [IntType]; (Operation (l, BitNot, [w], ts), IntType, None)
      | UintPtrType -> ts := Some [UintPtrType]; (Operation (l, BitNot, [w], ts), UintPtrType, None)
      | _ -> static_error l "argument to ~ must be char, short, int or uintptr" None
      end
    | Operation (l, (Le | Lt as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote l e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, (Add | Sub as operator), [e1; e2], ts) ->
      let (w1, t1, value1) = check e1 in
      let (w2, t2, value2) = check e2 in
      let t1 = unfold_inferred_type t1 in
      let t2 = unfold_inferred_type t2 in
      begin
        match t1 with
          PtrType pt1 ->
          begin match t2 with
            PtrType pt2 when operator = Sub ->
            if pt1 <> pt2 then static_error l "Pointers must be of same type" None;
            if pt1 <> Char && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported" None;
            ts:=Some [t1; t2];
            (Operation (l, operator, [w1; w2], ts), IntType, None)
          | _ ->
            let w2 = checkt e2 intt in
            ts:=Some [t1; IntType];
            (Operation (l, operator, [w1; w2], ts), t1, None)
          end
        | IntType | RealType | ShortType | Char | UintPtrType ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (Operation (l, operator, [w1; w2], ts), t, if t = IntType then (match (value1, value2) with ((Some value1), (Some value2)) -> begin match operator with Add -> Some(add_big_int value1 value2) | Sub -> Some(sub_big_int value1 value2) end | _-> None) else None)
        | ObjType "java.lang.String" as t when operator = Add ->
          let w2 = checkt e2 t in
          ts:=Some [t1; ObjType "java.lang.String"];
          (Operation (l, operator, [w1; w2], ts), t1, None)
        | _ -> static_error l ("Operand of addition or subtraction must be pointer, integer, char, short, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2)) None
      end
    | Operation (l, Mul, [e1; e2], ts) ->
      let (w1, w2, t) = promote l e1 e2 ts in
      begin match t with PtrType _ -> static_error l "Cannot multiply pointers." None | _ -> () end;
      (Operation (l, Mul, [w1; w2], ts), t, None)
    | Operation (l, Div, [e1; e2], ts) ->
      let (w1, w2, t) = promote l e1 e2 ts in
      begin match t with PtrType _ -> static_error l "Cannot divide pointers." None | _ -> () end;
      (Operation (l, Div, [w1; w2], ts), t, None)
    | Operation (l, (ShiftLeft | ShiftRight as op), [e1; e2], ts) ->
      let w1 = checkt e1 IntType in
      let w2 = checkt e2 IntType in
      ts := Some [IntType; IntType];
      (Operation (l, op, [w1; w2], ts), IntType, None)
    | IntLit (l, n, t) -> (e, (match !t with None -> t := Some intt; intt | Some t -> t), Some n)
    | RealLit(l, n) -> (e, RealType, None)
    | ClassLit (l, s) ->
      let s = check_classname (pn, ilist) (l, s) in
      (ClassLit (l, s), ObjType "java.lang.Class", None)
    | StringLit (l, s) -> (match file_type path with
        Java-> (e, ObjType "java.lang.String", None)
      | _ -> (e, (PtrType Char), None))
    | CastExpr (l, truncating, te, e) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let w = checkt_cast e t in
      (CastExpr (l, truncating, ManifestTypeExpr (type_expr_loc te, t), w), t, None)
    | Read (l, e, f) ->
      check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f
    | Deref (l, e, tr) ->
      let (w, t, _) = check e in
      begin
        match t with
          PtrType t0 -> tr := Some t0; (Deref (l, w, tr), t0, None)
        | _ -> static_error l "Operand must be pointer." None
      end
    | AddressOf (l, Var(l2, x, scope)) when List.mem_assoc x tenv ->
      scope := Some(LocalVar); (Var(l2, x, scope), PtrType(match List.assoc x tenv with RefType(t) -> t | _ -> static_error l "Taking the address of this expression is not supported." None), None)
    | AddressOf (l, e) -> let (w, t, _) = check e in (AddressOf (l, w), PtrType t, None)
    | CallExpr (l, "getClass", [], [], [LitPat target], Instance) when language = Java ->
      let w = checkt target (ObjType "java.lang.Object") in
      (WMethodCall (l, "java.lang.Object", "getClass", [], [w], Instance), ObjType "java.lang.Class", None)
    | ExprCallExpr (l, e, es) ->
      let (w, t, _) = check e in
      begin match (t, es) with
        (PureFuncType (_, _), _) -> check_pure_fun_value_call l w t es
      | (ClassOrInterfaceName(cn), [e2]) -> check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (CastExpr(l, false, IdentTypeExpr(expr_loc e, None, cn), e2))
      | _ -> static_error l "The callee of a call of this form must be a pure function value." None
      end 
    | CallExpr (l, g, targes, [], pats, fb) ->
      let es = List.map (function LitPat e -> e | _ -> static_error l "Patterns are not allowed in this position" None) pats in
      let process_targes callee_tparams =
        if callee_tparams <> [] && targes = [] then
          let targs = List.map (fun _ -> InferredType (ref None)) callee_tparams in
          let Some tpenv = zip callee_tparams targs in
          (targs, tpenv)
        else
          let targs = List.map (check_pure_type (pn,ilist) tparams) targes in
          let tpenv =
            match zip callee_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          (targs, tpenv)
      in
      let func_call () =
        match try_assoc g tenv with
          Some (PtrType (FuncType ftn)) ->
          let (_, gh, tparams, rt, ftxmap, xmap, pre, post, ft_predfammap) = List.assoc ftn functypemap in
          let rt = match rt with None -> Void | Some rt -> rt in (* This depends on the fact that the return type does not mention type parameters. *)
          (WFunPtrCall (l, g, es), rt, None)
        | Some ((PureFuncType (t1, t2) as t)) ->
          if targes <> [] then static_error l "Pure function value does not have type parameters." None;
          check_pure_fun_value_call l (Var (l, g, ref (Some LocalVar))) t es
        | _ ->
        match (g, es) with
          ("malloc", [SizeofExpr (ls, StructTypeExpr (lt, tn))]) ->
          if not (List.mem_assoc tn structmap) then static_error lt "No such struct" None;
          (WFunCall (l, g, [], es), PtrType (StructType tn), None)
        | _ ->
        match resolve (pn,ilist) l g funcmap with
          Some (g, FuncInfo (funenv, fterm, lg, k, callee_tparams, tr, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, fbf, v)) ->
          let (targs, tpenv) = process_targes callee_tparams in
          let rt0 = match tr with None -> Void | Some rt -> rt in
          let rt = instantiate_type tpenv rt0 in
          (WFunCall (l, g, targs, es), rt, None)
        | None ->
        match resolve (pn,ilist) l g purefuncmap with
          Some (g, (_, callee_tparams, t0, ts, _)) ->
          let (targs, tpenv) = process_targes callee_tparams in
          let pts =
            match zip es ts with
              None -> static_error l "Incorrect argument count." None
            | Some pts -> pts
          in
          let args = List.map (fun (e, t0) -> let t = instantiate_type tpenv t0 in box (checkt e t) t t0) pts in
          let t = instantiate_type tpenv t0 in
          (unbox (WPureFunCall (l, g, targs, args)) t0 t, t, None)
        | None ->
          static_error l (match language with CLang -> "No such function" | Java -> "No such method or function") None
      in
      if language = CLang || classmap = [] then func_call () else
      let try_qualified_call tn es args fb on_fail =
        let ms = get_methods tn g in
        if ms = [] then on_fail () else
        let argtps = List.map (fun e -> let (_, tp, _) = (check e) in tp) args in
        let ms = List.filter (fun (sign, _) -> is_assignable_to_sign argtps sign) ms in
        begin match ms with
          [] -> static_error l "No matching method" None
        | [(sign, (tn', lm, gh, rt, xmap, pre, post, epost, fb', v, abstract))] ->
          let (fb, es) = if fb = Instance && fb' = Static then (Static, List.tl es) else (fb, es) in
          if fb <> fb' then static_error l "Instance method requires target object" None;
          let rt = match rt with None -> Void | Some rt -> rt in
          (WMethodCall (l, tn', g, sign, es, fb), rt, None)
        | _ -> static_error l "Multiple matching overloads" None
        end
      in
      begin match fb with
        Static ->
        begin fun on_fail ->
          match try_assoc "this" tenv with
            Some (ObjType cn) ->
            try_qualified_call cn (Var (l, "this", ref (Some LocalVar))::es) es Instance on_fail
          | _ ->
          match try_assoc current_class tenv with
            Some (ClassOrInterfaceName tn) ->
            try_qualified_call tn es es Static on_fail
          | _ ->
          on_fail ()
        end $. fun () ->
        func_call ()
      | Instance ->
        let arg0e::args = es in
        let (_, arg0tp, _) = check arg0e in
        let (tn, es, fb) =
          match unfold_inferred_type arg0tp with
            ObjType tn -> (tn, es, Instance)
          | ClassOrInterfaceName tn -> (tn, List.tl es, Static)
          | _ -> static_error l "Target of method call must be object or class" None
        in
        try_qualified_call tn es args fb (fun () -> static_error l "No such method" None)
      end
    | NewObject (l, cn, args) ->
      begin match resolve (pn,ilist) l cn classmap with
        Some (cn, {cabstract}) ->
        if cabstract then
          static_error l "Cannot create instance of abstract class." None
        else 
          (NewObject (l, cn, args), ObjType cn, None)
      | None -> static_error l "No such class" None
      end
    | ReadArray(l, arr, index) ->
      let (w1, arr_t, _) = check arr in
      let w2 = checkt index intt in
      begin match unfold_inferred_type arr_t with
        ArrayType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | StaticArrayType (tp, _) -> (WReadArray (l, w1, tp, w2), tp, None)
      | PtrType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | _ when language = Java -> static_error l "Target of array access is not an array." None
      | _ when language = CLang -> static_error l "Target of array access is not an array or pointer." None
      end
    | NewArray (l, te, len) ->
      let t = check_pure_type (pn,ilist) tparams te in
      ignore $. checkt len IntType;
      (e, (ArrayType t), None)
    | NewArrayWithInitializer (l, te, es) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let ws = List.map (fun e -> checkt e t) es in
      (e, ArrayType t, None)
    | IfExpr (l, e1, e2, e3) ->
      let w1 = checkt e1 boolt in
      let (w2, t, _) = check e2 in
      let w3 = checkt e3 t in
      (IfExpr (l, w1, w2, w3), t, None)
    | SwitchExpr (l, e, cs, cdef_opt, tref) ->
      let (w, t, _) = check e in
      begin
        match t with
          InductiveType (i, targs) ->
          begin
            let (_, inductive_tparams, ctormap, _) = List.assoc i inductivemap in
            let (Some tpenv) = zip inductive_tparams targs in
            let rec iter t0 wcs ctors cs =
              match cs with
                [] ->
                let (t0, wcdef_opt) =
                  match cdef_opt with
                    None ->
                    if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors)) None;
                    (t0, None)
                  | Some (lcdef, edef) ->
                    if ctors = [] then static_error lcdef "Superfluous default clause" None;
                    let (wdef, tdef, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv edef in
                    let t0 =
                      match t0 with
                        None -> Some tdef
                      | Some t0 -> expect_type (expr_loc edef) tdef t0; Some t0
                    in
                    (t0, Some (lcdef, wdef))
                in
                begin
                  match t0 with
                    None -> static_error l "Switch expressions with zero clauses are not yet supported." None
                  | Some t0 -> tref := Some (t, tenv, targs, t0); (SwitchExpr (l, w, wcs, wcdef_opt, tref), t0, None)
                end
              | SwitchExprClause (lc, cn, xs, e)::cs ->
                begin
                  match try_assoc cn ctormap with
                    None ->
                    static_error lc ("Not a constructor of inductive type '" ^ i ^ "'.") None
                  | Some (_, (_, _, _, ts, _)) ->
                    if not (List.mem_assoc cn ctors) then static_error lc "Duplicate clause." None;
                    let xenv =
                      let rec iter2 ts xs xenv =
                        match (ts, xs) with
                          ([], []) -> List.rev xenv
                        | (t::ts, []) -> static_error lc "Too few pattern variables." None
                        | ([], _) -> static_error lc "Too many pattern variables." None
                        | (t::ts, x::xs) ->
                          if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
                          if List.mem_assoc x xenv then static_error lc "Duplicate pattern variable." None;
                          iter2 ts xs ((x, instantiate_type tpenv t)::xenv)
                      in
                      iter2 ts xs []
                    in
                    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams (xenv@tenv) e in
                    let t0 =
                      match t0 with
                        None -> Some t
                      | Some t0 -> expect_type (expr_loc e) t t0; Some t0
                    in
                    let ctors = List.filter (fun (ctorname, _) -> ctorname <> cn) ctors in
                    iter t0 (SwitchExprClause (lc, cn, xs, w)::wcs) ctors cs
                end
            in
            iter None [] ctormap cs
          end
        | _ -> static_error l "Switch expression operand must be inductive value." None
      end
    | SizeofExpr(l, te) ->
      let t = check_pure_type (pn,ilist) tparams te in
      (SizeofExpr (l, ManifestTypeExpr (type_expr_loc te, t)), IntType, None)
    | InstanceOfExpr(l, e, te) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let w = checkt e (ObjType "java.lang.Object") in
      (InstanceOfExpr (l, w, ManifestTypeExpr (type_expr_loc te, t)), boolt, None)
    | SuperMethodCall(l, mn, args) ->
      let rec get_implemented_instance_method cn mn argtps =
        if cn = "java.lang.Object" then None else
        match try_assoc cn classmap with 
        | Some {cmeths; csuper} ->
          begin try
            let m =
              List.find
                begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract)) ->
                  mn = mn' &&  is_assignable_to_sign argtps sign && not abstract
                end
                cmeths
            in
            Some m
          with Not_found ->
            get_implemented_instance_method csuper mn argtps
          end
        | None -> None
      in
      let args_checked = List.map (fun a -> let (w, tp, _) = check a in (w, tp)) args in 
      let argtps = List.map snd args_checked in
      let wargs = List.map fst args_checked in
      let thistype = try_assoc "this" tenv in
      begin match thistype with
        None -> static_error l "super calls not allowed in static context." None
      | Some(ObjType(cn)) -> 
        begin match try_assoc cn classmap with
          None -> static_error l "No matching method." None
        | Some {csuper} ->
            begin match get_implemented_instance_method csuper mn argtps with
              None -> static_error l "No matching method." None
            | Some(((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract))) -> 
             (WSuperMethodCall(l, mn, (Var (l, "this", ref (Some LocalVar))) :: wargs, (lm, gh, rt, xmap, pre, post, epost, v)), (match rt with Some(tp) -> tp | _ -> Void), None)
            end
        end
      end 
    | AssignExpr (l, e1, e2) ->
      let (w1, t1, _) = check e1 in
      let w2 = checkt e2 t1 in
      (AssignExpr (l, w1, w2), t1, None)
    | AssignOpExpr(l, e1, (Add | Sub | Mul as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      lhs_type := Some t1;
      let (w2, t2, _) = check e2 in
      begin
        match t1 with
          PtrType pt1 when operator = Add || operator = Sub ->
          begin match t2 with
            PtrType pt2 when operator = Sub ->
            if pt1 <> pt2 then static_error l "Pointers must be of same type" None;
            if pt1 <> Char && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported" None;
            ts:=Some [t1; t2];
            (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), IntType, None)
          | _ ->
            let w2 = checkt e2 intt in
            ts:=Some [t1; IntType];
            (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
          end
        | IntType | RealType | ShortType | Char ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
        | ObjType "java.lang.String" as t when operator = Add ->
          let w2 = checkt e2 t in
          ts:=Some [t1; ObjType "java.lang.String"];
          (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
        | _ -> static_error l ("Operand of addition, subtraction or multiplication must be pointer, integer, char, short, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2)) None
      end
    | AssignOpExpr(l, e1, (And | Or | Xor as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      lhs_type := Some t1;
      ts := Some [t1; t2];
      begin match (t1, t2) with
        ((Bool, Bool)) -> (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
      | ((Char|ShortType|IntType), (Char|ShortType|IntType)) ->
        (AssignOpExpr(l, w1, (match operator with And -> BitAnd | Or -> BitOr | Xor -> BitXor), w2, postOp, ts, lhs_type), IntType, None)
       | _ -> static_error l "Arguments to &=, &= and ^= must be boolean or integral types." None
      end
    | AssignOpExpr(l, e1, (ShiftLeft | ShiftRight | Div | Mod as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      if t1 <> IntType then static_error (expr_loc e1) "Variable of type int expected" None;
      let w2 = checkt e2 IntType in
      lhs_type := Some IntType;
      ts := Some [IntType; IntType];
      (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), IntType, None)
    | e -> static_error (expr_loc e) "Expression form not allowed here." None
  and check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 =
    check_expr_t_core_core functypemap funcmap classmap interfmap (pn, ilist) tparams tenv e t0 false
  and check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 isCast =
    match (e, unfold_inferred_type t0) with
      (Operation(l, Div, [IntLit(_, i1, _); IntLit(_, i2, _)], _), RealType) -> RealLit(l, (num_of_big_int i1) // (num_of_big_int i2))
    | (IntLit (l, n, t), PtrType _) when isCast || eq_big_int n zero_big_int -> t:=Some t0; e
    | (IntLit (l, n, t), UintPtrType) -> t:=Some UintPtrType; e
    | (IntLit (l, n, t), RealType) -> t:=Some RealType; e
    | (IntLit (l, n, t), UChar) ->
      t:=Some UChar;
      if not (le_big_int min_uchar_big_int n && le_big_int n max_uchar_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as uchar must be between 0 and 255." None
      else
        e
    | (IntLit (l, n, t), Char) ->
      t:=Some Char;
      if not (le_big_int min_char_big_int n && le_big_int n max_char_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
          let n = if 128 <= n then n - 256 else n in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as char must be between -128 and 127." None
      else
        e
    | (IntLit (l, n, t), UShortType) ->
      t:=Some UShortType;
      if not (le_big_int min_ushort_big_int n && le_big_int n max_ushort_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as ushort must be between 0 and 65535." None
      else
        e
    | (IntLit (l, n, t), ShortType) ->
      t:=Some ShortType;
      if not (le_big_int min_short_big_int n && le_big_int n max_short_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
          let n = if 32768 <= n then n - 65536 else n in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as short must be between -32768 and 32767." None
      else
        e
    | (IntLit (l, n, t), UintPtrType) ->
      t:=Some UintPtrType;
      if not (le_big_int min_ptr_big_int n && le_big_int n max_ptr_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_string "4294967296")) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as ushort must be between 0 and 65535." None
      else
        e  
    | _ ->
      let (w, t, value) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
      let check () = begin match (t, t0) with
          (ObjType _, ObjType _) when isCast -> w
        | (PtrType _, UintPtrType) when isCast -> w
        | (UintPtrType, PtrType _) when isCast -> w
        | (IntType, Char) when isCast -> w
        | (IntType, UChar) when isCast -> w
        | (IntType, ShortType) when isCast -> w
        | (IntType, UShortType) when isCast -> w
        | (IntType, UintPtrType) when isCast -> w
        | (UintPtrType, Char) when isCast -> w
        | (UintPtrType, UChar) when isCast -> w
        | (UintPtrType, ShortType) when isCast -> w
        | (UintPtrType, UShortType) when isCast -> w
        | (UintPtrType, IntType) when isCast -> w
        | (ShortType, UChar) when isCast -> w
        | (ShortType, Char) when isCast -> w
        | (ShortType, UShortType) when isCast -> w
        | (UShortType, UChar) when isCast -> w
        | (UShortType, Char) when isCast -> w
        | (UShortType, ShortType) when isCast -> w
        | (Char, UChar) when isCast -> w
        | (UChar, Char) when isCast -> w
        | (ObjType ("java.lang.Object"), ArrayType _) when isCast -> w
        | _ ->
          expect_type (expr_loc e) t t0;
          if try expect_type dummy_loc t0 t; false with StaticError _ -> true then
            Upcast (w, t, t0)
          else
            w
        end
      in
      match (value, t, t0) with
        (Some(value), IntType, Char) when le_big_int min_char_big_int value && le_big_int value max_char_big_int -> w
      | (Some(value), IntType, ShortType) when le_big_int min_short_big_int value && le_big_int value max_short_big_int -> w
      | _ -> check ()
  and check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f =
    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    begin
    match unfold_inferred_type t with
    | PtrType (StructType sn) ->
      begin
      match List.assoc sn structmap with
        (_, Some fds, _) ->
        begin
          match try_assoc f fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.") None
          | Some (_, gh, t) -> (WRead (l, w, sn, f, t, false, ref (Some None), gh), t, None)
        end
      | (_, None, _) -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' was declared without a body.") None
      end
    | ObjType cn ->
      begin
      match lookup_class_field cn f with
        None -> static_error l ("No such field in class '" ^ cn ^ "'.") None
      | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
        if fbinding = Static then static_error l "Accessing a static field via an instance is not supported." None;
        let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
        in
        (WRead (l, w, fclass, f, ft, false, ref (Some None), fgh), ft, constant_value)
      end
    | ArrayType _ when f = "length" ->
      (ArrayLengthExpr (l, w), IntType, None)
    | ClassOrInterfaceName cn ->
      begin match lookup_class_field cn f with
        None -> static_error l "No such field" None
      | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
        if fbinding = Instance then static_error l "You cannot access an instance field without specifying a target object." None;
        let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
         in
        (WRead (l, w, fclass, f, ft, true, fvalue, fgh), ft, constant_value)
      end
    | PackageName pn ->
      let name = pn ^ "." ^ f in
      if List.mem_assoc name classmap1 || List.mem_assoc name interfmap1 || List.mem_assoc name classmap0 || List.mem_assoc name interfmap0 then
        (e, ClassOrInterfaceName name, None)
      else if is_package name then
        (e, PackageName name, None)
      else
        static_error l "No such type or package" None
    | _ -> static_error l "Target expression of field dereference should be of type pointer-to-struct." None
    end
  in
  
  let check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e =
   let (w, tp, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
   (w, tp)
  in
  
  let check_expr (pn,ilist) tparams tenv e = check_expr_core [] [] [] [] (pn,ilist) tparams tenv e in
  let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core [] [] [] [] (pn,ilist) tparams tenv e tp in
  
  (* Region: Type checking of fixpoint function bodies *)

  let fixpointmap1 =
    let rec iter fpm_done fpm_todo =
      match fpm_todo with
        [] -> List.rev fpm_done
      | (g, (l, tparams, rt, pmap, index, body, pn, ilist, fsym))::fpm_todo ->
      match (index, body) with
        (Some index, SwitchStmt (ls, Var (lx, x, _), cs)) ->
        let (i, targs) =
          match List.assoc x pmap with
            InductiveType (i, targs) -> (i, targs)
          | _ -> static_error l "Switch operand is not an inductive value." None
        in
        let (_, inductive_tparams, ctormap, _) = List.assoc i inductivemap in
        let (Some tpenv) = zip inductive_tparams targs in
        let rec check_cs ctormap wcs cs =
          match cs with
            [] ->
            begin match ctormap with
              [] -> ()
            | (cn, _)::_ ->
              static_error ls ("Missing case: '" ^ cn ^ "'.") None
            end;
            wcs
          | SwitchStmtClause (lc, e, body)::cs ->
            let (cn, xs) =
              match e with
                CallExpr (_, cn, _, _, pats, _) ->
                let xs = List.map (function LitPat (Var (_, x, _)) -> x | _ -> static_error lc "Constructor arguments must be variable names" None) pats in
                (cn, xs)
              | Var (_, cn, _) -> (cn, [])
              | _ -> static_error lc "Case expression must be constructor pattern" None
            in
            let ts =
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor." None
              | Some (_, (_, _, _, ts, _)) -> ts
            in
            let xmap =
              let rec iter xmap ts xs =
                match (ts, xs) with
                  ([], []) -> xmap
                | (t::ts, x::xs) ->
                  if List.mem_assoc x pmap then static_error lc "Pattern variable hides parameter." None;
                  let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." None in
                  iter ((x, instantiate_type tpenv t)::xmap) ts xs
                | ([], _) -> static_error lc "Too many pattern variables." None
                | _ -> static_error lc "Too few pattern variables." None
              in
              iter [] ts xs
            in
            let tenv = xmap @ pmap in
            let (lret, body) =
              match body with
                [ReturnStmt (lret, Some e)] -> (lret, e)
              | _ -> static_error lc "Body of switch clause must be a return statement with a result expression." None
            in
            let wbody = check_expr_t (pn,ilist) tparams tenv body rt in
            let rec iter0 components e =
              let rec iter () e =
                let iter1 e = iter () e in
                match e with
                  WPureFunCall (l, g', targs, args) ->
                  if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
                  if g' = g then begin
                    match List.nth args index with
                      Var (l, x, _) when List.mem x components -> ()
                    | _ -> static_error l "Inductive argument of recursive call must be switch clause pattern variable." None
                  end;
                  List.iter iter1 args
                | Var (l, g', scope) when (match !scope with Some PureFuncName -> true | _ -> false) ->
                  if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
                  if g' = g then static_error l "A fixpoint function that mentions itself is not yet supported." None
                | SwitchExpr (l, Var (_, x, _), cs, def_opt, _) when List.mem x components ->
                  List.iter (fun (SwitchExprClause (_, _, pats, e)) -> iter0 (pats @ components) e) cs;
                  (match def_opt with None -> () | Some (l, e) -> iter1 e)
                | _ -> expr_fold_open iter () e
              in
              iter () e
            in
            iter0 (List.map fst xmap) wbody;
            check_cs (List.remove_assoc cn ctormap) (SwitchExprClause (lc, cn, xs, wbody)::wcs) cs
        in
        let wcs = check_cs ctormap [] cs in
        iter ((g, (l, rt, pmap, Some index, SwitchExpr (ls, Var (lx, x, ref None), wcs, None, ref None), pn, ilist, fsym))::fpm_done) fpm_todo
      | (None, ReturnStmt (lr, Some e)) ->
        let tenv = pmap in
        let w = check_expr_t (pn,ilist) tparams tenv e rt in
        let rec iter0 e =
          let rec iter () e =
            let iter1 e = iter () e in
            match e with
              WPureFunCall (l, g', targs, args) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot call itself." None;
              List.iter iter1 args
            | Var (l, g', scope) when (match !scope with Some PureFuncName -> true | _ -> false) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot mention itself." None
            | _ -> expr_fold_open iter () e
          in
          iter () e
        in
        iter0 w;
        iter ((g, (l, rt, pmap, None, w, pn, ilist, fsym))::fpm_done) fpm_todo
    in
    iter [] fixpointmap1
  in
  
  (* Static field initializers cannot have side-effects; otherwise, class initialization would be tricky to verify. *)
  let check_static_field_initializer e =
    let rec iter e =
      match e with
        True _ | False _ | Null _ | Var _ | IntLit _ | RealLit _ | StringLit _ | ClassLit _ -> ()
      | Operation (l, _, es, _) -> List.iter iter es
      | NewArray (l, t, e) -> iter e
      | NewArrayWithInitializer (l, t, es) -> List.iter iter es
      | CastExpr (l, _, _, e) -> iter e
      | Upcast (e, _, _) -> iter e
      | WRead (_, e, _, _, _, _, _, _) -> iter e
      | _ -> static_error (expr_loc e) "This expression form is not supported in a static field initializer." None
    in
    iter e
  in
  
  (* Region: Type checking of field initializers for static fields *)
  
  let classmap1 =
    List.map
      begin fun (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist)) ->
        let fds =
          List.map
            begin function
              (f, ({ft; fbinding=Static; finit=Some e} as fd)) ->
                let e = check_expr_t (pn,ilist) [] [current_class, ClassOrInterfaceName cn] e ft in
                check_static_field_initializer e;
                (f, {fd with finit=Some e})
            | fd -> fd
            end
            fds
        in
        (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist))
      end
      classmap1
  in
  
  let rec check_c_initializer e tp =
    match tp, e with
    | StaticArrayType (Char, n), StringLit (ls, s) ->
      if String.length s + 1 > n then static_error ls "String literal does not fit inside character array." None;
      e
    | StaticArrayType (elemTp, elemCount), InitializerList (ll, es) ->
      let rec iter n es =
        match es with
          [] -> []
        | e::es ->
          if n = 0 then static_error ll "Initializer list too long." None;
          let e = check_c_initializer e elemTp in
          let es = iter (n - 1) es in
          e::es
      in
      InitializerList (ll, iter elemCount es)
    | StructType sn, InitializerList (ll, es) ->
      let fds =
        match List.assoc sn structmap with
          (_, Some fds, _) -> fds
        | _ -> static_error ll "Cannot initialize struct declared without a body." None
      in
      let rec iter fds es =
        match fds, es with
          _, [] -> []
        | (_, (_, Ghost, _))::fds, es -> iter fds es
        | (_, (_, _, tp))::fds, e::es ->
          let e = check_c_initializer e tp in
          let es = iter fds es in
          e::es
        | _ -> static_error ll "Initializer list too long." None
      in
      InitializerList (ll, iter fds es)
    | tp, e ->
      check_expr_t ("", []) [] [] e tp
  in
  
  globalmap1 |> List.iter begin fun (x, (lg, tp, symb, ref_init)) ->
    ref_init := option_map (fun e -> check_c_initializer e tp) !ref_init
  end;
  
  (* Region: Computing constant field values *)
  
  begin
    let string_of_const v =
      match v with
        IntConst n -> string_of_big_int n
      | BoolConst b -> if b then "true" else "false"
      | StringConst s -> s
      | NullConst -> "null"
    in
    let rec eval callers e =
      let ev = eval callers in
      match e with
        True l -> BoolConst true
      | False l -> BoolConst false
      | Null l -> NullConst
      | Operation (l, Add, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (add_big_int n1 n2)
        | (StringConst s1, v) -> StringConst (s1 ^ string_of_const v)
        | (v, StringConst s2) -> StringConst (string_of_const v ^ s2)
        | _ -> raise NotAConstant
        end
      | Operation (l, Sub, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (sub_big_int n1 n2)
        | _ -> raise NotAConstant
        end
      | Operation (l, Mul, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (mult_big_int n1 n2)
        | _ -> raise NotAConstant
        end
      | IntLit (l, n, _) -> IntConst n
      | StringLit (l, s) -> StringConst s
      | WRead (l, _, fparent, fname, _, fstatic, _, _) when fstatic -> eval_field callers (fparent, fname)
      | CastExpr (l, truncating, ManifestTypeExpr (_, t), e) ->
        let v = ev e in
        begin match (t, v) with
          (Char, IntConst n) ->
          let n =
            if not (le_big_int (big_int_of_int (-128)) n && le_big_int n (big_int_of_int 127)) then
              let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
              let n = if 128 <= n then n - 256 else n in
              big_int_of_int n
            else
              n
          in
          IntConst n
        | (ShortType, IntConst n) ->
          let n =
            if not (le_big_int (big_int_of_int (-32768)) n && le_big_int n (big_int_of_int 32767)) then
              let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
              let n = if 32768 <= n then n - 65536 else n in
              big_int_of_int n
            else
              n
          in
          IntConst n
        | _ -> raise NotAConstant
        end
      | Upcast (e, fromType, toType) -> ev e
      | WidenedParameterArgument e -> ev e
      | _ -> raise NotAConstant
    and eval_field callers ((cn, fn) as f) =
      if List.mem f callers then raise NotAConstant;
      match try_assoc cn classmap1 with
        Some (l, abstract, fin, meths, fds, const, super, interfs, preds, pn, ilist) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn classmap0 with
        Some {cfds} -> eval_field_body (f::callers) (List.assoc fn cfds)
      | None ->
      match try_assoc cn interfmap1 with
        Some (li, fds, meths, preds, interfs, pn, ilist) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn interfmap0 with
        Some (InterfaceInfo (li, fields, meths, preds, interfs)) -> eval_field_body (f::callers) (List.assoc fn fields)
      | None ->
      assert false
    and eval_field_body callers {fbinding; ffinal; finit; fvalue} =
      match !fvalue with
        Some None -> raise NotAConstant
      | Some (Some v) -> v
      | None ->
        match (fbinding, ffinal, finit) with
          (Static, true, Some e) ->
          begin try
            let v = eval callers e in
            fvalue := Some (Some v);
            v
          with NotAConstant -> fvalue := Some None; raise NotAConstant
          end
        | _ -> fvalue := Some None; raise NotAConstant
    in
    let compute_fields fds =
      fds |> List.iter (fun (f, fbody) -> try ignore $. eval_field_body [] fbody with NotAConstant -> ())
    in
    classmap1 |> List.iter (fun (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist)) -> compute_fields fds);
    interfmap1 |> List.iter (fun (ifn, (li, fds, meths, preds, interfs, pn, ilist)) -> compute_fields fds)
  end;
  
  (* Region: type checking of assertions *)
  
  let check_pat_core (pn,ilist) l tparams tenv t p =
    match p with
      LitPat (WidenedParameterArgument e) ->
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      expect_type l t tp;
      (LitPat (WidenedParameterArgument w), [])
    | LitPat e -> let w = check_expr_t (pn,ilist) tparams tenv e t in (LitPat w, [])
    | VarPat x ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
      (p, [(x, t)])
    | DummyPat -> (p, [])
  in
  
  let check_pat (pn,ilist) l tparams tenv t p = let (w, tenv') = check_pat_core (pn,ilist) l tparams tenv t p in (w, tenv' @ tenv) in

  let merge_tenvs l tenv1 tenv2 =
    let rec iter tenv1 tenv3 =
      match tenv1 with
        [] -> tenv3
      | ((x, t) as xt)::tenv1 ->
        if List.mem_assoc x tenv2 then static_error l (Printf.sprintf "Variable name clash: '%s'" x) None;
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
    | ([], _) -> static_error l "Too many patterns" None
    | (_, []) -> static_error l "Too few patterns" None
  in
    
  let get_class_of_this =
    WMethodCall (dummy_loc, "java.lang.Object", "getClass", [], [Var (dummy_loc, "this", ref (Some LocalVar))], Instance)
  in
  
  let get_class_finality tn = (* Returns ExtensibleClass if tn is an interface *)
    match try_assoc tn classmap1 with
      Some (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
      fin
    | None ->
      match try_assoc tn classmap0 with
        Some {cfinal} ->
        cfinal
      | None -> ExtensibleClass
  in
  
  let check_inst_pred_asn l cn g check_call error =
    let rec find_in_interf itf =
      let search_interfmap get_interfs_and_preds interfmap fallback =
        match try_assoc itf interfmap with
          Some info ->
          let (interfs, preds) = get_interfs_and_preds info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb) -> [(family, pmap)]
          | None -> List.flatten (List.map (fun i -> find_in_interf i) interfs)
          end
        | None -> fallback ()
      in
      search_interfmap (function (li, fields, meths, preds, interfs, pn, ilist) -> (interfs, preds)) interfmap1 $. fun () ->
      search_interfmap (function InterfaceInfo (li, fields, meths, preds, interfs) -> (interfs, preds)) interfmap0 $. fun () ->
      []
    in
    let rec find_in_class cn =
      let search_classmap classmap proj fallback =
        match try_assoc cn classmap with
          Some info ->
          let (super, interfs, preds) = proj info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb, body) -> [(family, pmap)]
          | None -> find_in_class super @ flatmap find_in_interf interfs
          end
        | None -> fallback ()
      in
      search_classmap classmap1
        (function (_, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) -> (super, interfs, preds))
        $. fun () ->
      search_classmap classmap0
        (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
        $. fun () ->
      []
    in
    begin match find_in_class cn @ find_in_interf cn with
      [] -> error ()
    | [(family, pmap)] -> check_call family pmap
    | _ -> static_error l (Printf.sprintf "Ambiguous instance predicate assertion: multiple predicates named '%s' in scope" g) None
    end
  in
  
  let rec check_asn_core (pn,ilist) tparams tenv p =
    let check_asn = check_asn_core in
    match p with
      PointsTo (l, lhs, v) ->
      let (wlhs, t) = check_expr (pn,ilist) tparams tenv lhs in
      begin match wlhs with
        WRead (_, _, _, _, _, _, _, _) | WReadArray (_, _, _, _) -> ()
      | _ -> static_error l "The left-hand side of a points-to assertion must be a field dereference or an array element expression." None
      end;
      let (wv, tenv') = check_pat (pn,ilist) l tparams tenv t v in
      (WPointsTo (l, wlhs, t, wv), tenv', [])
    | PredAsn (l, p, targs, ps0, ps) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      begin fun cont ->
         match try_assoc p#name tenv with
           Some (PredType (callee_tparams, ts, inputParamCount)) -> cont (new predref (p#name), false, callee_tparams, [], ts, inputParamCount)
         | None | Some _ ->
          begin match resolve (pn,ilist) l p#name predfammap with
            Some (pname, (_, callee_tparams, arity, xs, _, inputParamCount)) ->
            let ts0 = match file_type path with
              Java-> list_make arity (ObjType "java.lang.Class")
            | _   -> list_make arity (PtrType Void)
            in
            cont (new predref pname, true, callee_tparams, ts0, xs, inputParamCount)
          | None ->
            begin match
              match try_assoc p#name predctormap1 with
                Some (l, ps1, ps2, body, funcsym, pn, ilist) -> Some (ps1, ps2)
              | None ->
              match try_assoc p#name predctormap0 with
                Some (PredCtorInfo (l, ps1, ps2, body, funcsym)) -> Some (ps1, ps2)
              | None -> None
            with
              Some (ps1, ps2) ->
              cont (new predref (p#name), true, [], List.map snd ps1, List.map snd ps2, None)
            | None ->
              let error () = 
                begin match try_assoc p#name tenv with
                  None ->  static_error l ("No such predicate: " ^ p#name) None 
                | Some _ -> static_error l ("Variable " ^ p#name ^ " is not of predicate type.") None 
                end
              in
              begin match try_assoc "this" tenv with
                None -> error ()
              | Some (ObjType cn) ->
                let check_call family pmap =
                  if targs <> [] then static_error l "Incorrect number of type arguments." None;
                  if ps0 <> [] then static_error l "Incorrect number of indices." None;
                  let (wps, tenv) = check_pats (pn,ilist) l tparams tenv (List.map snd pmap) ps in
                  let index =
                    if List.mem_assoc cn classmap1 || List.mem_assoc cn classmap0 then
                      ClassLit (l, cn)
                    else
                      get_class_of_this
                  in
                  (WInstPredAsn (l, None, cn, get_class_finality cn, family, p#name, index, wps), tenv, [])
                in
                check_inst_pred_asn l cn p#name check_call error
              | Some(_) -> error ()
              end
            end
          end
      end $. fun (p, is_global_predref, callee_tparams, ts0, xs, inputParamCount) ->
      begin
        let (targs, tpenv, inferredTypes) =
          if targs = [] then
            let tpenv = List.map (fun x -> (x, ref None)) callee_tparams in
            (List.map (fun (x, r) -> InferredType r) tpenv,
             List.map (fun (x, r) -> (x, InferredType r)) tpenv,
             List.map (fun (x, r) -> r) tpenv)
          else
            match zip callee_tparams targs with
              None -> static_error l (Printf.sprintf "Predicate requires %d type arguments." (List.length callee_tparams)) None
            | Some bs -> (targs, bs, [])
        in
        if List.length ps0 <> List.length ts0 then static_error l "Incorrect number of indexes." None;
        let (wps0, tenv) = check_pats (pn,ilist) l tparams tenv ts0 ps0 in
        let xs' = List.map (instantiate_type tpenv) xs in
        let (wps, tenv) = check_pats (pn,ilist) l tparams tenv xs' ps in
        p#set_domain (ts0 @ xs'); p#set_inputParamCount inputParamCount;
        (WPredAsn (l, p, is_global_predref, targs, wps0, wps), tenv, inferredTypes)
      end
    | InstPredAsn (l, e, g, index, pats) ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      begin match unfold_inferred_type t with
        ObjType cn ->
        let check_call family pmap =
          let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv (List.map snd pmap) pats in
          let index = check_expr_t (pn,ilist) tparams tenv index (ObjType "java.lang.Class") in
          (WInstPredAsn (l, Some w, cn, get_class_finality cn, family, g, index, wpats), tenv, [])
        in
        let error () = static_error l (Printf.sprintf "Type '%s' does not declare such a predicate" cn) None in
        check_inst_pred_asn l cn g check_call error
      | _ -> static_error l "Target of instance predicate assertion must be of class type" None
      end
    | ExprAsn (l, e) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in (ExprAsn (l, w), tenv, [])
    | Sep (l, p1, p2) ->
      let (p1, tenv, infTps1) = check_asn (pn,ilist) tparams tenv p1 in
      let (p2, tenv, infTps2) = check_asn (pn,ilist) tparams tenv p2 in
      (Sep (l, p1, p2), tenv, infTps1 @ infTps2)
    | IfAsn (l, e, p1, p2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let (wp1, _, infTps1) = check_asn (pn,ilist) tparams tenv p1 in
      let (wp2, _, infTps2) = check_asn (pn,ilist) tparams tenv p2 in
      (IfAsn (l, w, wp1, wp2), tenv, infTps1 @ infTps2)
    | SwitchAsn (l, e, cs) ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      begin
      match t with
      | InductiveType (i, targs) ->
        begin
        match try_assoc i inductivemap with
          None -> static_error l "Switch operand is not an inductive value." None
        | Some (_, inductive_tparams, ctormap, _) ->
          let (Some tpenv) = zip inductive_tparams targs in
          let rec iter wcs ctormap cs infTps =
            match cs with
              [] ->
              let _ = 
                match ctormap with
                  [] -> ()
                | (cn, _)::_ ->
                  static_error l ("Missing case: '" ^ cn ^ "'.") None
              in (WSwitchAsn (l, w, i, wcs), tenv, infTps)
            | SwitchAsnClause (lc, cn, xs, ref_xsInfo, body)::cs ->
              begin
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor." None
              | Some (_, (_, _, _, ts, _)) ->
                let (xmap, xsInfo) =
                  let rec iter xmap xsInfo ts xs =
                    match (ts, xs) with
                      ([], []) -> (xmap, List.rev xsInfo)
                    | (t::ts, x::xs) ->
                      if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
                      let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." None in
                      let xInfo = match unfold_inferred_type t with TypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None in
                      iter ((x, instantiate_type tpenv t)::xmap) (xInfo::xsInfo) ts xs
                    | ([], _) -> static_error lc "Too many pattern variables." None
                    | _ -> static_error lc "Too few pattern variables." None
                  in
                  iter [] [] ts xs
                in
                ref_xsInfo := Some xsInfo;
                let tenv = xmap @ tenv in
                let (wbody, _, clauseInfTps) = check_asn (pn,ilist)  tparams tenv body in
                iter (SwitchAsnClause (lc, cn, xs, ref_xsInfo, wbody)::wcs) (List.remove_assoc cn ctormap) cs (clauseInfTps @ infTps)
              end
          in
          iter [] ctormap cs []
        end
      | _ -> static_error l "Switch operand is not an inductive value." None
      end
    | EmpAsn l -> (p, tenv, [])
    | CoefAsn (l, coef, body) ->
      let (wcoef, tenv') = check_pat_core (pn,ilist) l tparams tenv RealType coef in
      let (wbody, tenv, infTps) = check_asn (pn,ilist) tparams tenv body in
      (CoefAsn (l, wcoef, wbody), merge_tenvs l tenv' tenv, infTps)
    | PluginAsn (l, text) ->
      match pluginmap with
        [] -> static_error l "Load a plugin before using a plugin assertion" None
      | [_, ((plugin, _), _)] ->
        let to_plugin_type t =
          match t with
            PtrType (StructType sn) -> Plugins.StructPointerType sn
          | PluginInternalType t -> Plugins.PluginInternalType t
          | _ -> Plugins.VeriFastInternalType
        in
        let from_plugin_type t =
          match t with
            Plugins.StructPointerType sn -> PtrType (StructType sn)
          | Plugins.VeriFastInternalType -> failwith "plugin_typecheck_assertion must not create binding with type VeriFastInternalType"
          | Plugins.PluginInternalType t -> PluginInternalType t
        in        
        let plugin_tenv = List.map (fun (x, t) -> (x, to_plugin_type t)) tenv in
        begin try
          let (w, plugin_bindings) = plugin#typecheck_assertion plugin_tenv text in
          let bindings = List.map (fun (x, t) -> (x, from_plugin_type t)) plugin_bindings in
          (WPluginAsn (l, List.map fst bindings, w), bindings @ tenv, [])
        with
          Plugins.PluginStaticError (off, len, msg) ->
          let ((path, line, col), _) = l in
          let l = ((path, line, col + 1 + off), (path, line, col + 1 + off + len)) in (* TODO: Suport multiline assertions *)
          static_error l msg None
        end
  in
  
  let rec fix_inferred_type r =
    match !r with
      None -> r := Some Bool (* any type will do *)
    | Some (InferredType r) -> fix_inferred_type r
    | _ -> ()
  in
  
  let fix_inferred_types rs = List.iter fix_inferred_type rs in
  
  let check_asn (pn,ilist) tparams tenv p =
    let (wpred, tenv, infTypes) = check_asn_core (pn,ilist) tparams tenv p in
    fix_inferred_types infTypes;
    (wpred, tenv)
  in
  
  let boxmap =
    List.map
      begin
        fun (bcn, (l, boxpmap, inv, amap, hpmap,pn,ilist)) ->
        let (winv, boxvarmap) = check_asn (pn,ilist) [] boxpmap inv in
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
    let rec iter state e =
      match e with
      | Var (l, x, scope) -> begin match !scope with Some LocalVar -> x::state | Some _ -> state end
      | SwitchExpr (l, e, cs, cdef_opt, _) ->
        vars_used e @
        flatmap
          (fun (SwitchExprClause (l, c, xs, e)) ->
           let xs' = vars_used e in
           List.filter (fun x -> not (List.mem x xs)) xs'
          )
          cs @
        (match cdef_opt with None -> [] | Some (l, e) -> vars_used e) @
        state
      | e -> expr_fold_open iter state e
    in
    iter [] e
  in
  
  let assert_expr_fixed fixed e =
    let used = vars_used e in
    let nonfixed = List.filter (fun x -> not (List.mem x fixed)) used in
    if nonfixed <> [] then
      let xs = String.concat ", " (List.map (fun x -> "'" ^ x ^ "'") nonfixed) in
      static_error (expr_loc e) ("Preciseness check failure: non-fixed variable(s) " ^ xs ^ " used in input expression.") None
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
    List.iter (function (LitPat e) -> assert_expr_fixed fixed e | _ -> static_error l "Non-fixed pattern used in input position." None) pats
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
      WPointsTo (l, lhs, tp, pv) ->
      begin match lhs with
        WRead (lr, et, _, _, _, _, _, _) -> assert_expr_fixed fixed et
      | WReadArray (la, ea, tp, ei) -> assert_expr_fixed fixed ea; assert_expr_fixed fixed ei
      end;
      assume_pat_fixed fixed pv
    | WPredAsn (l, g, is_global_predref, targs, pats0, pats) ->
      begin
        match g#inputParamCount with
          None -> static_error l "Preciseness check failure: callee is not precise." (Some "calleeisnotprecise")
        | Some n ->
          let (inpats, outpats) = take_drop n pats in
          let inpats = pats0 @ inpats in
          assert_pats_fixed l fixed inpats;
          assume_pats_fixed fixed outpats
      end
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
      begin match e_opt with None -> () | Some e -> assert_expr_fixed fixed e end;
      assert_expr_fixed fixed index;
      assume_pats_fixed fixed pats
    | ExprAsn (l, Operation (_, Eq, [Var (_, x, scope); e2], _)) when !scope = Some LocalVar ->
      if not (List.mem x fixed) && expr_is_fixed fixed e2 then
        x::fixed
      else
        fixed
    | ExprAsn (_, _) -> fixed
    | Sep (l, p1, p2) ->
      let fixed = check_pred_precise fixed p1 in
      check_pred_precise fixed p2
    | IfAsn (l, e, p1, p2) ->
      assert_expr_fixed fixed e;
      let fixed1 = check_pred_precise fixed p1 in
      let fixed2 = check_pred_precise fixed p2 in
      intersect fixed1 fixed2
    | WSwitchAsn (l, e, i, cs) ->
      assert_expr_fixed fixed e;
      let rec iter fixed' cs =
        match cs with
          [] -> get fixed'
        | SwitchAsnClause (l, c, xs, _, p)::cs ->
          let fixed = check_pred_precise (xs@fixed) p in
          iter (Some (match fixed' with None -> fixed | Some fixed' -> intersect fixed' fixed)) cs
      in
      iter None cs
    | EmpAsn l -> fixed
    | CoefAsn (l, coefpat, p) ->
      begin
        match coefpat with
          LitPat e -> assert_expr_fixed fixed e
        | VarPat x -> static_error l "Precision check failure: variable patterns not supported as coefficients." None
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
                let (g, (_, _, _, _, symb, _)) = List.assoc (sn, f) field_pred_map in
                let predinst p =
                  p#set_inputParamCount (Some 1);
                  ((g, []),
                   ([], l, [], [sn, PtrType (StructType sn); "value", t], symb, Some 1,
                    let r = WRead (l, Var (l, sn, ref (Some LocalVar)), sn, f, t, false, ref (Some None), Real) in
                    WPredAsn (l, p, true, [], [], [LitPat (AddressOf (l, r)); LitPat (Var (l, "value", ref (Some LocalVar)))])
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
  
  let check_predinst0 predfam_tparams arity ps psymb inputParamCount (pn, ilist) tparams tenv env l p predinst_tparams fns xs body =
    check_tparams l tparams predinst_tparams;
    let tpenv =
      match zip predfam_tparams (List.map (fun x -> TypeParam x) predinst_tparams) with
        None -> static_error l "Number of type parameters does not match predicate family." None
      | Some bs -> bs
    in
    if List.length fns <> arity then static_error l "Incorrect number of indexes." None;
    let pxs =
      match zip ps xs with
        None -> static_error l "Incorrect number of parameters." None
      | Some pxs -> pxs
    in
    let tparams' = predinst_tparams @ tparams in
    let xs =
      let rec iter2 xm pxs =
        match pxs with
          [] -> List.rev xm
        | (t0, (te, x))::xs -> 
          let t = check_pure_type (pn,ilist) tparams' te in
          expect_type l t (instantiate_type tpenv t0);
          if List.mem_assoc x tenv then static_error l ("Parameter '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
          if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
          iter2 ((x, t)::xm) xs
      in
      iter2 [] pxs
    in
    let (wbody, _) = check_asn (pn,ilist) tparams' (xs @ tenv) body in
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
             static_error l ("Preciseness check failure: body does not fix output parameter '" ^ x ^ "'.") None)
          outps
    end;
    ((p, fns), (env, l, predinst_tparams, xs, psymb, inputParamCount, wbody))
  in
  
  let check_predinst (pn, ilist) tparams tenv env l p predinst_tparams fns xs body =
    let (p, predfam_tparams, arity, ps, psymb, inputParamCount) =
      match resolve (pn,ilist) l p predfammap with
        None -> static_error l ("No such predicate family: "^p) None
      | Some (p, (_, predfam_tparams, arity, ps, psymb, inputParamCount)) -> (p, predfam_tparams, arity, ps, psymb, inputParamCount)
    in
    check_predinst0 predfam_tparams arity ps psymb inputParamCount (pn, ilist) tparams tenv env l p predinst_tparams fns xs body
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
        let _ = if List.mem_assoc pfns pm || List.mem_assoc pfns predinstmap0 then static_error l "Duplicate predicate family instance." None in
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
  
  let predctormap1 =
    List.map
      (
        function
          (g, (l, ps1, ps2, body, funcsym,pn,ilist)) ->
          let (wbody, _) = check_asn (pn,ilist) [] (ps1 @ ps2) body in
          (g, PredCtorInfo (l, ps1, ps2, wbody, funcsym))
      )
      predctormap1
  in
  
  let predctormap = predctormap1 @ predctormap0 in
  
  let classmap1 =
    classmap1 |> List.map
      begin fun (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist)) ->
        let preds =
          preds |> List.map
            begin function
              (g, (l, pmap, family, symb, Some body)) ->
              let tenv = (current_class, ClassOrInterfaceName cn)::("this", ObjType cn)::pmap in
              let (wbody, _) = check_asn (pn,ilist) [] tenv body in
              let fixed = check_pred_precise ["this"] wbody in
              List.iter
                begin fun (x, t) ->
                  if not (List.mem x fixed) then static_error l ("Preciseness check failure: predicate body does not fix parameter '" ^ x ^ "'.") None
                end
                pmap;
              (g, (l, pmap, family, symb, Some wbody))
            | pred -> pred
            end
        in
        (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist))
      end
  in
  
  (* Region: evaluation helpers; pushing and popping assumptions and execution trace elements *)
  
  let check_ghost ghostenv l e =
    expr_iter
      begin function
        Var (l, x, _) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context." None
      | _ -> ()
      end
      e
  in

  let funcnameterms = List.map (fun fn -> (fn, get_unique_var_symb fn (PtrType Void))) funcnames
  in
  
  let struct_sizes =
    List.map
      begin fun (sn, _) ->
        let s = get_unique_var_symb ("struct_" ^ sn ^ "_size") IntType in
        ignore $. ctxt#assume (ctxt#mk_lt (ctxt#mk_intlit 0) s);
        (sn, s)
      end
      structmap
  in
  
  let rec sizeof l t =
    match t with
      Void | Char | UChar -> ctxt#mk_intlit 1
    | IntType | UintPtrType -> ctxt#mk_intlit 4
    | PtrType _ -> ctxt#mk_intlit 4
    | StructType sn -> List.assoc sn struct_sizes
    | StaticArrayType (elemTp, elemCount) -> ctxt#mk_mul (sizeof l elemTp) (ctxt#mk_intlit elemCount)
    | _ -> static_error l ("Taking the size of type " ^ string_of_type t ^ " is not yet supported.") None
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
  
  let field_offset l fparent fname =
    match try_assoc (fparent, fname) field_offsets with
      Some term -> term
    | None -> static_error l "Cannot take the address of a ghost field" None
  in
  let field_address l t fparent fname = ctxt#mk_add t (field_offset l fparent fname) in
  
  let convert_provertype term proverType proverType0 =
    if proverType = proverType0 then term else apply_conversion proverType proverType0 term
  in
  
  let prover_convert_term term t t0 =
    if t = t0 then term else convert_provertype term (provertype_of_type t) (provertype_of_type t0)
  in
  
  let get_pred_symb p = let (_, _, _, _, symb, _) = List.assoc p predfammap in symb in
  
  let lazy_value f =
    let cell = ref None in
    fun () ->
      match !cell with
        None -> let result = f() in cell := Some result; result
      | Some result -> result
  in
  let lazy_predfamsymb name = lazy_value (fun () -> get_pred_symb name) in
  
  let array_element_symb = lazy_predfamsymb "java.lang.array_element" in
  let array_slice_symb = lazy_predfamsymb "java.lang.array_slice" in
  let array_slice_deep_symb = lazy_predfamsymb "java.lang.array_slice_deep" in
  
  let mk_nil () =
    let (_, _, _, _, nil_symb) = List.assoc "nil" purefuncmap in
    mk_app nil_symb []
  in
  
  let mk_cons elem_tp head tail =
    let (_, _, _, _, cons_symb) = List.assoc "cons" purefuncmap in
    mk_app cons_symb [apply_conversion (provertype_of_type elem_tp) ProverInductive head; tail]
  in
  
  let mk_all_eq elem_tp xs x =
    let (_, _, _, _, all_eq_symb) = List.assoc "all_eq" purefuncmap in
    mk_app all_eq_symb [xs; apply_conversion (provertype_of_type elem_tp) ProverInductive x]
  in
  
  let rec mk_list elem_tp elems =
    match elems with
      [] -> mk_nil()
    | e::es -> mk_cons elem_tp e (mk_list elem_tp es)
  in
  
  let mk_take n xs =
    let (_, _, _, _, take_symb) = List.assoc "take" purefuncmap in
    mk_app take_symb [n; xs]
  in
  
  let mk_drop n xs =
    let (_, _, _, _, drop_symb) = List.assoc "drop" purefuncmap in
    mk_app drop_symb [n; xs]
  in
  
  let mk_append l1 l2 =
    let (_, _, _, _, append_symb) = List.assoc "append" purefuncmap in
    mk_app append_symb [l1; l2]
  in
  
  let mk_length l =
    let (_, _, _, _, length_symb) = List.assoc "length" purefuncmap in
    mk_app length_symb [l]
  in
  
  let rec mk_zero_list n =
    assert (0 <= n);
    if n = 0 then
      mk_nil ()
    else
      mk_cons Char (ctxt#mk_intlit 0) (mk_zero_list (n - 1))
  in
  
  let mk_char_list_of_c_string size s =
    let n = String.length s in
    let rec iter k =
      if k = n then
        mk_zero_list (size - n)
      else
        mk_cons Char (ctxt#mk_intlit (Char.code s.[k])) (iter (k + 1))
    in
    iter 0
  in
  
  let contextStack = ref [] in
  
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
  
  let pprint_context_term t = 
    if options.option_simplify_terms then
      match ctxt#simplify t with None -> ctxt#pprint t | Some(t) -> ctxt#pprint t
    else
      ctxt#pprint t
  in
  
  let pprint_context_stack cs =
    List.map
      (function
         Assuming t -> Assuming (pprint_context_term t)
       | Executing (h, env, l, msg) ->
         let h' =
           List.map
             begin function
               (Chunk ((g, literal), targs, coef, ts, Some (PluginChunkInfo info))) ->
               let [_, ((_, plugin), _)] = pluginmap in
               Chunk ((ctxt#pprint g, literal), targs, pprint_context_term coef, [plugin#string_of_state info], None)
             | (Chunk ((g, literal), targs, coef, ts, size)) ->
               Chunk ((ctxt#pprint g, literal), targs, pprint_context_term coef, List.map (fun t -> pprint_context_term t) ts, size)
             end
             h
         in
         let env' = List.map (fun (x, t) -> (x, pprint_context_term t)) env in
         Executing (h', env', l, msg)
       | PushSubcontext -> PushSubcontext
       | PopSubcontext -> PopSubcontext)
      cs
  in

  let assert_term t h env l msg url = 
    stats#proverOtherQuery;
    if not (ctxt#query t) then
      raise (SymbolicExecutionError (pprint_context_stack !contextStack, ctxt#pprint t, l, msg, url))
  in

  let assert_false h env l msg url =
    raise (SymbolicExecutionError (pprint_context_stack !contextStack, "false", l, msg, url))
  in
  
  let rec prover_type_term l tp = 
    match tp with
      ObjType(n) -> 
      begin match try_assoc n classterms with
        None -> (match try_assoc n interfaceterms with None -> static_error l ("unknown prover_type_expr for: " ^ (string_of_type tp)) None | Some(t) -> t)
      | Some(t) -> t
      end
    | ArrayType(tp) -> (ctxt#mk_app array_type_symbol [prover_type_term l tp])
    | _ -> static_error l ("unknown prover_type_expr for: " ^ (string_of_type tp)) None
  in

  (* Region: evaluation *)
  
  let eval_op l op v1 v2 ts ass_term =
     let check_overflow l min t max =
      begin
      match ass_term with
        Some assert_term when not disable_overflow_check ->
        assert_term l (ctxt#mk_le min t) "Potential arithmetic underflow." (Some "potentialarithmeticunderflow");
        assert_term l (ctxt#mk_le t max) "Potential arithmetic overflow." (Some "potentialarithmeticoverflow")
      | _ -> ()
      end;
      t
    in
    let bounds = if ass_term = None then (* in ghost code, where integer types do not imply limits *) None else 
    match ts with
      Some ([UintPtrType; _] | [_; UintPtrType]) -> Some (int_zero_term, max_ptr_term)
    | Some ([IntType; _] | [_; IntType]) -> Some (min_int_term, max_int_term)
    | Some ([ShortType; _] | [_; ShortType]) -> Some (min_short_term, max_short_term)
    | Some ([Char; _] | [_; Char]) -> Some (min_char_term, max_char_term)
    | _ -> None
    in
    begin match op with
      And -> ctxt#mk_and v1 v2
    | Or -> ctxt#mk_or v1 v2
    | Eq ->
      let Some [tp1; tp2] = ts in
      if (tp1, tp2) = (Bool, Bool) then
        ctxt#mk_iff v1 v2
      else
        ctxt#mk_eq v1 v2
    | Neq -> ctxt#mk_not (ctxt#mk_eq v1 v2)
    | Add ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_add v1 v2) max_int_term
      | (PtrType t, IntType) ->
        let n = sizeof l t in
        check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_add v1 (ctxt#mk_mul n v2)) max_ptr_term
      | (RealType, RealType) ->
        ctxt#mk_real_add v1 v2
      | (ShortType, ShortType) ->
        check_overflow l min_short_term (ctxt#mk_add v1 v2) max_short_term
      | (Char, Char) ->
        check_overflow l min_char_term (ctxt#mk_add v1 v2) max_char_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_add v1 v2) max_uint_term
      | _ -> static_error l "Internal error in eval." None
      end
    | Sub ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_sub v1 v2) max_int_term
      | (PtrType t, IntType) ->
        let n = sizeof l t in
        check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_sub v1 (ctxt#mk_mul n v2)) max_ptr_term
      | (RealType, RealType) ->
        ctxt#mk_real_sub v1 v2
      | (ShortType, ShortType) ->
        check_overflow l min_short_term (ctxt#mk_sub v1 v2) max_short_term
      | (Char, Char) ->
        check_overflow l min_char_term (ctxt#mk_sub v1 v2) max_char_term
      | (PtrType (Char | Void), PtrType (Char | Void)) ->
        check_overflow l min_int_term (ctxt#mk_sub v1 v2) max_int_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_sub v1 v2) max_uint_term
      end
    | Mul ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_mul v1 v2) max_int_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_mul v1 v2) max_uint_term
      | (RealType, RealType) ->
        ctxt#mk_real_mul v1 v2
      end
    | Le ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        ((IntType, IntType) | (PtrType _, PtrType _) |
              (UintPtrType, UintPtrType)) -> ctxt#mk_le v1 v2
      | (RealType, RealType) -> ctxt#mk_real_le v1 v2
      end
    | Lt ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        ((IntType, IntType) | (PtrType _, PtrType _) |
              (UintPtrType, UintPtrType)) -> ctxt#mk_lt v1 v2
      | (RealType, RealType) -> ctxt#mk_real_lt v1 v2
      end
    | Div ->
      begin match ts with
        Some ([RealType; RealType]) -> static_error l "Realdiv not supported yet in /=." None
      | Some ([IntType; IntType]) -> 
        begin match ass_term with
          Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None
        | None -> ()
        end;
        (ctxt#mk_div v1 v2)
      end
    | BitAnd | BitXor | BitOr ->
      let symb = match op with
          BitAnd -> bitwise_and_symbol
        | BitXor -> bitwise_xor_symbol
        | BitOr -> bitwise_or_symbol
      in
      let app = ctxt#mk_app symb [v1;v2] in
      begin match bounds with
        None -> ()
      | Some(min_term, max_term) -> 
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_term app) (ctxt#mk_le app max_term)));
      end;
      app
    | ShiftRight -> 
      let app = ctxt#mk_app shiftright_symbol [v1;v2] in
      begin match bounds with
        None -> ()
      | Some(min_term, max_term) -> 
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_term app) (ctxt#mk_le app max_term)));
      end;
      app
    | Mod -> ctxt#mk_mod v1 v2
    | ShiftLeft when ts = Some [IntType; IntType] -> ctxt#mk_app shiftleft_int32_symbol [v1;v2]
    | _ -> static_error l "This operator is not supported in this position." None
    end
  in
  
  let rec eval_core_cps0 eval_core ev state ass_term read_field env e cont =
     let evs state es cont =
      let rec iter state vs es =
        match es with
          [] -> cont state (List.rev vs)
        | e::es -> ev state e $. fun state v -> iter state (v::vs) es
      in
      iter state [] es
    in
    let check_overflow l min t max =
      begin
      match ass_term with
        Some assert_term when not disable_overflow_check ->
        assert_term l (ctxt#mk_le min t) "Potential arithmetic underflow." (Some "potentialarithmeticunderflow");
        assert_term l (ctxt#mk_le t max) "Potential arithmetic overflow." (Some "potentialarithmeticoverflow")
      | _ -> ()
      end;
      t
    in
    match e with
      True l -> cont state ctxt#mk_true
    | False l -> cont state ctxt#mk_false
    | Null l -> cont state (ctxt#mk_intlit 0)
    | Var (l, x, scope) ->
      cont state
      begin
        if !scope = None then print_endline (string_of_loc l);
        let (Some scope) = !scope in
        match scope with
          LocalVar -> (try List.assoc x env with Not_found -> assert_false [] env l (Printf.sprintf "Unbound variable '%s'" x) None)
        | PureCtor -> let Some (lg, tparams, t, [], s) = try_assoc x purefuncmap in mk_app s []
        | FuncName -> List.assoc x funcnameterms
        | PredFamName -> let Some (_, _, _, _, symb, _) = try_assoc x predfammap in symb
        | EnumElemName n -> ctxt#mk_intlit_of_string (string_of_big_int n)
        | GlobalName ->
          let Some((_, tp, symbol, init)) = try_assoc x globalmap in 
          begin match tp with
            StaticArrayType (_, _) -> symbol
          | _ -> 
          begin
            match read_field with
              None -> static_error l "Cannot mention global variables in this context." None
            | Some (read_field, read_static_field, deref_pointer, read_array) ->
              deref_pointer l symbol tp
          end
          end
        | ModuleName -> List.assoc x modulemap
        | PureFuncName -> let (lg, tparams, t, tps, (fsymb, vsymb)) = List.assoc x purefuncmap in vsymb
      end
    | PredNameExpr (l, g) -> let Some (_, _, _, _, symb, _) = try_assoc g predfammap in cont state symb
    | CastExpr (l, truncating, ManifestTypeExpr (_, t), e) ->
      begin
        match (e, t, truncating) with
          (IntLit (_, n, _), PtrType _, _) ->
          if ass_term <> None && not (le_big_int zero_big_int n &&
le_big_int n max_ptr_big_int) then static_error l "CastExpr: Int literal is out of range." None;
          cont state (ctxt#mk_intlit_of_string (string_of_big_int n))
        | (e, Char, false) ->
          ev state e $. fun state t ->
          cont state (check_overflow l min_char_term t max_char_term)
        | (e, ShortType, false) ->
          ev state e $. fun state t ->
          cont state (check_overflow l min_short_term t max_short_term)
        | (e, Char, true) ->
          ev state e $. fun state t ->
          cont state (ctxt#mk_app truncate_int8_symbol [t])
        | (e, ShortType, true) ->
          ev state e $. fun state t ->
          cont state (ctxt#mk_app truncate_int16_symbol [t])
        | (_, (ObjType _|ArrayType _), _) when ass_term = None -> static_error l "Class casts are not allowed in annotations." None
        | _ -> ev state e cont (* No other cast allowed by the type checker changes the value *)
      end
    | Upcast (e, fromType, toType) -> ev state e cont
    | WidenedParameterArgument e -> ev state e cont
    | RealLit(l, n) ->
      cont state begin 
        if eq_num n (num_of_big_int unit_big_int) then
        real_unit
            else
        ctxt#mk_reallit_of_num n
      end
    | IntLit (l, n, t) ->
      begin match !t with
        Some RealType ->
        cont state
          begin
            if eq_big_int n unit_big_int then
              real_unit
            else
              ctxt#mk_reallit_of_num (num_of_big_int n)
          end
      | Some t ->
        if ass_term <> None then
        begin
          let (min, max) =
            match t with 
              IntType -> (min_int_big_int, max_int_big_int)
            | UChar -> (min_uchar_big_int, max_uchar_big_int)
            | Char -> (min_char_big_int, max_char_big_int)
            | UShortType -> (min_ushort_big_int, max_ushort_big_int)
            | ShortType -> (min_short_big_int, max_short_big_int)
            | UintPtrType -> (zero_big_int, max_ptr_big_int)
            | PtrType _ -> (zero_big_int, max_ptr_big_int)
          in
          if not (le_big_int min n && le_big_int n max) then static_error l "IntLit: Int literal is out of range." None
        end;
        cont state
          begin
            try
              let n = int_of_big_int n in ctxt#mk_intlit n
            with Failure "int_of_big_int" -> ctxt#mk_intlit_of_string (string_of_big_int n)
          end
      end
    | ClassLit (l,s) -> cont state (List.assoc s classterms)
    | StringLit (l, s) -> 
      cont state
        begin match file_type path with
          Java -> get_unique_var_symb "stringLiteral" (ObjType "java.lang.String")
        | _ -> get_unique_var_symb "stringLiteral" (PtrType Char)
        end
    | WMethodCall (l, "java.lang.Object", "getClass", [], [target], Instance) ->
      ev state target $. fun state t ->
      cont state (ctxt#mk_app get_class_symbol [t])
    | WPureFunCall (l, g, targs, args) ->
      begin match try_assoc g purefuncmap with
        None -> static_error l ("No such pure function: "^g) None
      | Some (lg, tparams, t, pts, s) ->
        evs state args $. fun state vs ->
        cont state (mk_app s vs)
      end
    | WPureFunValueCall (l, e, es) ->
      evs state (e::es) $. fun state (f::args) ->
      cont state (List.fold_left (fun f arg -> ctxt#mk_app apply_symbol [f; arg]) f args)
    | IfExpr (l, e1, e2, e3) ->
      evs state [e1; e2; e3] $. fun state [v1; v2; v3] ->
      cont state (ctxt#mk_ifthenelse v1 v2 v3) (* Only sound if e2 and e3 are side-effect-free *)
    | Operation (l, BitAnd, [e1; Operation (_, BitNot, [e2], ts2)], ts1) ->
      ev state e1 $. fun state v1 -> ev state e2 $. fun state v2 ->
      cont state (ctxt#mk_app bitwise_and_symbol [v1; ctxt#mk_app bitwise_not_symbol [v2]])
    | Operation (l, Not, [e], ts) -> ev state e $. fun state v -> cont state (ctxt#mk_not v)
    | Operation (l, BitNot, [e], ts) ->
      begin match !ts with
        Some [IntType] -> ev state e $. fun state v -> cont state (ctxt#mk_app bitwise_not_symbol [v])
      | _ ->
        static_error l "VeriFast does not currently support taking the bitwise complement (~) of an unsigned integer except as part of a bitwise AND (x & ~y)." None
      end
    | Operation (l, Div, [e1; e2], ts) ->
      begin match ! ts with
        Some ([RealType; RealType]) ->
        begin match (e1, e2) with
          (RealLit (_, n), IntLit (_, d, _)) when eq_num n (num_of_big_int unit_big_int) && eq_big_int d two_big_int -> cont state real_half
        | (IntLit (_, n, _), IntLit (_, d, _)) when eq_big_int n unit_big_int && eq_big_int d two_big_int -> cont state real_half
        | _ -> 
          let rec eval_reallit e =
              match e with
              IntLit (l, n, t) -> num_of_big_int n
            | RealLit (l, n) -> n
            | _ -> static_error (expr_loc e) "The denominator of a division must be a literal." None
          in
          ev state e1 $. fun state v1 -> cont state (ctxt#mk_real_mul v1 (ctxt#mk_reallit_of_num (div_num (num_of_int 1) (eval_reallit e2)))) 
        end
      | Some ([IntType; IntType]) -> 
        ev state e1 $. fun state v1 -> ev state e2 $. fun state v2 -> 
        begin match ass_term with
          Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None
        | None -> ()
        end;
        cont state (ctxt#mk_div v1 v2)
      end
    | Operation (l, BitAnd, [e1; IntLit(_, i, _)], ts) when le_big_int zero_big_int i && ass_term <> None -> (* optimization *)
      ev state e1 $. fun state v1 ->
        let iterm = ctxt#mk_intlit (int_of_big_int i) in
        let app = ctxt#mk_app bitwise_and_symbol [v1;iterm] in
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le int_zero_term app) (ctxt#mk_le app iterm)));
        begin if eq_big_int i unit_big_int then
          ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_mod v1 (ctxt#mk_intlit 2)) app));
        end;
        cont state app
    | Operation (l, op, ([e1; e2] as es), ts) ->
      evs state es $. fun state [v1; v2] -> cont state (eval_op l op v1 v2 !ts ass_term) 
    | ArrayLengthExpr (l, e) ->
      ev state e $. fun state t ->
      begin match ass_term with
        Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq t (ctxt#mk_intlit 0))) "Target of array length expression might be null" None
      | None -> ()
      end;
      cont state (ctxt#mk_app arraylength_symbol [t])
    | WRead(l, e, fparent, fname, frange, fstatic, fvalue, fghost) ->
      if fstatic then
        cont state
          begin match !fvalue with
            Some (Some v) ->
            begin match v with
              IntConst n -> ctxt#mk_intlit_of_string (string_of_big_int n)
            | BoolConst b -> if b then ctxt#mk_true else ctxt#mk_false
            | StringConst s -> static_error l "String constants are not yet supported." None
            | NullConst -> ctxt#mk_intlit 0
            end
          | _ ->
            match read_field with
              None -> static_error l "Cannot use field read expression in this context." None
            | Some (read_field, read_static_field, deref_pointer, read_array) -> read_static_field l fparent fname
          end
      else
        ev state e $. fun state v ->
        begin
          match frange with
            StaticArrayType (elemTp, elemCount) ->
            cont state (field_address l v fparent fname)
          | _ ->
          match read_field with
            None -> static_error l "Cannot use field dereference in this context." None
          | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_field l v fparent fname)
        end
    | WReadArray(l, arr, tp, i) ->
      evs state [arr; i] $. fun state [arr; i] ->
      begin
        match read_field with
          None -> static_error l "Cannot use array indexing in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_array l arr i tp)
      end
    | Deref (l, e, t) ->
      ev state e $. fun state v ->
      begin
        match read_field with
          None -> static_error l "Cannot perform dereference in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) ->
          let (Some t) = !t in
          cont state (deref_pointer l v t)
      end
    | AddressOf (l, e) ->
      begin
        match e with
          WRead (le, e, fparent, fname, frange, fstatic, fvalue, fghost) -> 
          (* MS Visual C++ behavior: http://msdn.microsoft.com/en-us/library/hx1b6kkd.aspx (= depends on command-line switches and pragmas) *)
          (* GCC documentation is not clear about it. *)
          ev state e $. fun state v ->
          cont state (field_address l v fparent fname)
        | Var (l, x, scope) when !scope = Some GlobalName ->
          let Some (l, tp, symbol, init) = try_assoc x globalmap in cont state symbol
        | _ -> static_error l "Taking the address of this expression is not supported." None
      end
    | SwitchExpr (l, e, cs, cdef_opt, tref) ->
      let g = mk_ident "switch_expression" in
      ev state e $. fun state t ->
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
      let case_clauses = List.map (fun (SwitchExprClause (_, cn, ps, e)) -> (cn, (ps, e))) cs in
      let InductiveType (i, targs) = tt in
      let (_, _, ctormap, _) = List.assoc i inductivemap in
      let fpclauses =
        List.map
          begin fun (cn, (_, (_, tparams, _, pts, (csym, _)))) ->
            match try_assoc cn case_clauses with
              Some (ps, e) ->
              let apply (_::gvs) cvs =
                let Some genv = zip (List.map (fun (x, t) -> x) env) gvs in
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
                eval_core None None env e
              in
              (csym, apply)
            | None ->
              let (Some (_, e)) = cdef_opt in
              let apply gvs cvs =
                let Some genv = zip ("#value"::List.map (fun (x, t) -> x) env) gvs in
                eval_core None None genv e
              in
              (csym, apply)
          end
          ctormap
      in
      ctxt#set_fpclauses symbol 0 fpclauses;
      cont state (ctxt#mk_app symbol (t::List.map (fun (x, t) -> t) env))
    | ProverTypeConversion (tfrom, tto, e) -> ev state e $. fun state v -> cont state (convert_provertype v tfrom tto)
    | SizeofExpr (l, ManifestTypeExpr (_, t)) ->
      cont state (sizeof l t)
    | InstanceOfExpr(l, e, ManifestTypeExpr (l2, tp)) ->
      ev state e $. fun state v ->
        begin match tp with (* hack: if tp is a final class, then instanceof is translated as getClass *)
          ObjType(c) when get_class_finality c = FinalClass -> cont state (ctxt#mk_eq (prover_type_term l2 tp) (ctxt#mk_app get_class_symbol [v]))
        | _ -> cont state (ctxt#mk_app instanceof_symbol [v; prover_type_term l2 tp])
        end
    | _ -> static_error (expr_loc e) "Construct not supported in this position." None
  in
  
  let rec eval_core ass_term read_field env e =
    let rec ev () e cont = eval_core_cps0 eval_core ev () ass_term read_field env e cont in
    ev () e $. fun () v -> v
  in
  
  let eval_core_cps = eval_core_cps0 eval_core in
  
  let eval = eval_core None in

  let _ =
    List.iter
    begin function
       (g, (l, t, pmap, Some index, SwitchExpr (_, Var (_, x, _), cs, _, _), pn, ilist, fsym)) ->
       let rec index_of_param i x0 ps =
         match ps with
           [] -> assert false
         | (x, tp)::ps -> if x = x0 then (i, tp) else index_of_param (i + 1) x0 ps
       in
       let (i, InductiveType (_, targs)) = index_of_param 0 x pmap in
       let clauses =
         List.map
           (function SwitchExprClause (_, cn, pats, e) ->
              let (_, tparams, _, ts, (ctorsym, _)) = match try_assoc' (pn,ilist) cn purefuncmap with Some x -> x in
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
                eval None (patenv @ penv) e
              in
              (ctorsym, eval_body)
           )
           cs
       in
       ctxt#set_fpclauses fsym i clauses
     | (g, (l, t, pmap, None, w, pn, ilist, fsym)) ->
       ctxt#begin_formal;
       let env = imap (fun i (x, tp) -> let pt = typenode_of_type tp in (pt, (x, ctxt#mk_bound i pt))) pmap in
       let tps = List.map fst env in
       let env = List.map snd env in
       let rhs = eval None env w in
       let lhs = ctxt#mk_app fsym (List.map snd env) in
       ctxt#end_formal;
       ctxt#assume_forall [lhs] tps (ctxt#mk_eq lhs rhs)
    end
    fixpointmap1
  in
  
  (* Region: production of assertions *)
  
  let assert_expr env e h env l msg url = assert_term (eval None env e) h env l msg url in

  let success() = () in
  
  let branch cont1 cont2 =
    stats#branch;
    in_temporary_context (fun _ -> cont1());
    in_temporary_context (fun _ -> cont2())
  in
  
  let rec assert_expr_split e h env l msg url = 
    match e with
      IfExpr(l0, con, e1, e2) -> 
        branch
           (fun _ -> assume (eval None env con) (fun _ -> assert_expr_split e1 h env l msg url; ))
           (fun _ -> assume (ctxt#mk_not (eval None env con)) (fun _ -> assert_expr_split e2 h env l msg url; ))
    | Operation(l0, And, [e1; e2], tps) ->
        assert_expr_split e1 h env l msg url;
        assert_expr_split e2 h env l msg url;
    | _ -> with_context (Executing (h, env, expr_loc e, "Consuming expression")) (fun _ -> assert_expr env e h env l msg url)
  in
  
  let evalpat ghost ghostenv env pat tp0 tp cont =
    match pat with
      LitPat e -> cont ghostenv env (prover_convert_term (eval None env e) tp0 tp)
    | VarPat x -> let t = get_unique_var_symb_ x tp ghost in cont (x::ghostenv) (update env x (prover_convert_term t tp tp0)) t
    | DummyPat -> let t = get_unique_var_symb_ "dummy" tp ghost in cont ghostenv env t
  in
  
  let rec evalpats ghostenv env pats tps0 tps cont =
    match (pats, tps0, tps) with
      ([], [], []) -> cont ghostenv env []
    | (pat::pats, tp0::tps0, tp::tps) -> evalpat true ghostenv env pat tp0 tp (fun ghostenv env t -> evalpats ghostenv env pats tps0 tps (fun ghostenv env ts -> cont ghostenv env (t::ts)))
  in

  let real_mul l t1 t2 =
    if t1 == real_unit then t2 else if t2 == real_unit then t1 else
    let t = ctxt#mk_real_mul t1 t2 in
    if is_dummy_frac_term t1 || is_dummy_frac_term t2 then dummy_frac_terms := t::!dummy_frac_terms;
    t
  in
  
  let real_div l t1 t2 =
    if t2 == real_unit then t1 else static_error l "Real division not yet supported." None
  in
  
  let definitely_equal t1 t2 =
    let result = if t1 == t2 then (stats#definitelyEqualSameTerm; true) else (stats#definitelyEqualQuery; ctxt#query (ctxt#mk_eq t1 t2)) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  in
  
  let definitely_different t1 t2 =
    let result = if t1 == t2 then false else ctxt#query (ctxt#mk_not (ctxt#mk_eq t1 t2)) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  in
  
  let predname_eq g1 g2 =
    match (g1, g2) with
      ((g1, literal1), (g2, literal2)) -> if literal1 && literal2 then g1 == g2 else definitely_equal g1 g2
  in
  
  let assume_field h0 fparent fname frange fghost tp tv tcoef cont =
    let (_, (_, _, _, _, symb, _)) = List.assoc (fparent, fname) field_pred_map in
    if fghost = Real then begin
      match frange with
         Char -> ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_char_term tv) (ctxt#mk_le tv max_char_term)))
      | ShortType -> ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_short_term tv) (ctxt#mk_le tv max_short_term)))
      | IntType -> ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_int_term tv) (ctxt#mk_le tv max_int_term)))
      | PtrType _ | UintPtrType -> ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) tv) (ctxt#mk_le tv max_ptr_term)))
      | _ -> ()
    end; 
    (* automatic generation of t1 != t2 if t1.f |-> _ &*& t2.f |-> _ *)
    begin fun cont ->
      if tcoef != real_unit && tcoef != real_half then
        assume (ctxt#mk_real_lt real_zero tcoef) cont
      else
        cont()
    end $. fun () ->
    let pred_symb = (symb, true) in
    let rec iter h =
      match h with
        [] -> cont (Chunk ((symb, true), [], tcoef, [tp; tv], None)::h0)
      | Chunk (g, targs', tcoef', [tp'; tv'], _) as chunk::h when predname_eq g pred_symb ->
        if tcoef == real_unit || tcoef' == real_unit then
          assume_neq tp tp' (fun _ -> iter h)
        else if definitely_equal tp tp' then
        begin
          assume (ctxt#mk_eq tv tv') $. fun () ->
          let cont = (fun coef -> cont (Chunk ((symb, true), [], coef, [tp'; tv'], None)::List.filter (fun ch -> ch != chunk) h0)) in
          if tcoef == real_half && tcoef' == real_half then cont real_unit else
          if is_dummy_frac_term tcoef then
            cont tcoef'
          else if is_dummy_frac_term tcoef' then
            cont tcoef
          else
            let newcoef = (ctxt#mk_real_add tcoef tcoef') in (assume (ctxt#mk_real_le newcoef real_unit) $. fun () -> cont newcoef)
        end
        else
          iter h
      | _::h -> iter h
    in
    if (file_type path) <> Java || ctxt#query (ctxt#mk_not (ctxt#mk_eq tp (ctxt#mk_intlit 0))) then 
      iter h0
    else
      assume_neq tp (ctxt#mk_intlit 0) (fun _ -> iter h0) (* in Java, the target of a field chunk is non-null *)
  in

  let produce_chunk h g_symb targs coef inputParamCount ts size cont =
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
              if coef == real_half && coef' == real_half then real_unit else
              if is_dummy_frac_term coef then
                if is_dummy_frac_term coef' then
                  coef'
                else begin
                  ignore $. ctxt#assume (ctxt#mk_lt real_zero coef);
                  ctxt#mk_real_add coef coef'
                end
              else
                if is_dummy_frac_term coef' then begin
                  ignore $. ctxt#assume (ctxt#mk_lt real_zero coef');
                  ctxt#mk_real_add coef coef'
                end else
                  ctxt#mk_real_add coef coef'
            in
            cont (Chunk (g_symb, targs, coef, ts, size)::h)
          else
            iter (chunk::hdone) htodo
      in
      iter [] h
  in

  let rec produce_asn_core tpenv h ghostenv env p coef size_first size_all (assuming: bool) cont =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ ->
        if !verbosity >= 2 then Printf.printf "%10.6fs: %s: Producing assertion\n" (Perf.time()) (string_of_loc (asn_loc p));
        with_context (Executing (h, env, asn_loc p, "Producing assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval None env in
    match p with
    | WPointsTo (l, WRead (lr, e, fparent, fname, frange, fstatic, fvalue, fghost), tp, rhs) ->
      if fstatic then
        let (_, (_, _, _, _, symb, _)) = List.assoc (fparent, fname) field_pred_map in
        evalpat (fghost = Ghost) ghostenv env rhs tp tp $. fun ghostenv env t ->
        produce_chunk h (symb, true) [] coef (Some 0) [t] None $. fun h ->
        cont h ghostenv env
      else
        let te = ev e in
        evalpat (fghost = Ghost) ghostenv env rhs tp tp $. fun ghostenv env t ->
        assume_field h fparent fname frange fghost te t coef $. fun h ->
        cont h ghostenv env
    | WPointsTo (l, WReadArray (la, ea, _, ei), tp, rhs) ->
      let a = ev ea in
      let i = ev ei in
      evalpat false ghostenv env rhs tp tp $. fun ghostenv env t ->
      let slice = Chunk ((array_element_symb(), true), [tp], coef, [a; i; t], None) in
      cont (slice::h) ghostenv env
    | WPredAsn (l, g, is_global_predref, targs, pats0, pats) ->
      let (g_symb, pats0, pats, types, auto_info) =
        if not is_global_predref then 
          let Some term = try_assoc g#name env in ((term, false), pats0, pats, g#domain, None)
        else
          begin match try_assoc g#name predfammap with
            Some (_, _, _, declared_paramtypes, symb, _) -> ((symb, true), pats0, pats, g#domain, Some (g#name, declared_paramtypes))
          | None ->
            let PredCtorInfo (l, ps1, ps2, body, funcsym) = List.assoc g#name predctormap in
            let ctorargs = List.map (function LitPat e -> ev e | _ -> static_error l "Patterns are not supported in predicate constructor argument positions." None) pats0 in
            let g_symb = mk_app funcsym ctorargs in
            ((g_symb, false), [], pats, List.map snd ps2, None)
          end
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv types in
      evalpats ghostenv env (pats0 @ pats) types domain (fun ghostenv env ts ->
        let input_param_count = match g#inputParamCount with None -> None | Some c -> Some (c + (List.length pats0)) in
        let do_assume_chunk () = produce_chunk h g_symb targs coef input_param_count ts size_first (fun h -> cont h ghostenv env) in
        match
          if assuming then None else
          match auto_info with
            None -> None
          | Some (predName, declared_paramtypes) ->
            try
              Some (Hashtbl.find auto_lemmas predName, declared_paramtypes)
            with Not_found -> None
        with
          None -> do_assume_chunk ()
        | Some ((frac, tparams, xs1, xs2, pre, post), declared_paramtypes) ->
          let ts = List.map (fun (t, (tp0, tp)) -> prover_convert_term t tp0 tp) (zip2 ts (zip2 domain declared_paramtypes)) in
          match frac with
            None -> 
            if coef == real_unit then 
              produce_asn_core (zip2 tparams targs) h [] (zip2 (xs1@xs2) ts) post coef size_first size_all true (fun h_ _ _ -> cont h_ ghostenv env)
            else
              do_assume_chunk ()
          | Some(f) ->
            produce_asn_core (zip2 tparams targs) h [] ((f, coef) :: (zip2 (xs1@xs2) ts)) post real_unit size_first size_all true (fun h_ _ _ -> cont h_ ghostenv env)
      )
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
      let (pmap, pred_symb) =
        match try_assoc tn classmap1 with
          Some (lcn, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
          let (_, pmap, _, symb, _) = List.assoc g preds in (pmap, symb)
        | None ->
          match try_assoc tn classmap0 with
            Some {cpreds} ->
            let (_, pmap, _, symb, _) = List.assoc g cpreds in (pmap, symb)
          | None ->
            match try_assoc tn interfmap1 with
              Some (li, fields, methods, preds, interfs, pn, ilist) -> let (_, pmap, family, symb) = List.assoc g preds in (pmap, symb)
            | None ->
              let InterfaceInfo (li, fields, methods, preds, interfs) = List.assoc tn interfmap0 in
              let (_, pmap, family, symb) = List.assoc g preds in
              (pmap, symb)
      in
      let target = match e_opt with None -> List.assoc "this" env | Some e -> ev e in
      let index = ev index in
      assume (ctxt#mk_not (ctxt#mk_eq target (ctxt#mk_intlit 0))) $. fun () ->
      begin fun cont -> if cfin = FinalClass then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [target]) (List.assoc st classterms)) cont else cont () end $. fun () ->
      let types = List.map snd pmap in
      evalpats ghostenv env pats types types $. fun ghostenv env args ->
      produce_chunk h (pred_symb, true) [] coef (Some 2) (target::index::args) size_first $. fun h ->
      cont h ghostenv env
    | ExprAsn (l, e) -> assume (ev e) (fun _ -> cont h ghostenv env)
    | Sep (l, p1, p2) -> produce_asn_core tpenv h ghostenv env p1 coef size_first size_all assuming (fun h ghostenv env -> produce_asn_core tpenv h ghostenv env p2 coef size_all size_all assuming cont)
    | IfAsn (l, e, p1, p2) ->
      let cont h _ _ = cont h ghostenv env in
      branch
        (fun _ -> assume (ev e) (fun _ -> produce_asn_core tpenv h ghostenv env p1 coef size_all size_all assuming cont))
        (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> produce_asn_core tpenv h ghostenv env p2 coef size_all size_all assuming cont))
    | WSwitchAsn (l, e, i, cs) ->
      let cont h _ _ = cont h ghostenv env in
      let t = ev e in
      let (_, tparams, ctormap, _) = List.assoc i inductivemap in
      let rec iter cs =
        match cs with
          SwitchAsnClause (lc, cn, pats, patsInfo, p)::cs ->
          branch
            (fun _ ->
               let (_, (_, tparams, _, tps, cs)) = List.assoc cn ctormap in
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
               assume_eq t (mk_app cs (List.map (fun (x, t, _) -> t) xts)) (fun _ -> produce_asn_core tpenv h (pats @ ghostenv) (xenv @ env) p coef size_all size_all assuming cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpAsn l -> cont h ghostenv env
    | CoefAsn (l, DummyPat, body) ->
      produce_asn_core tpenv h ghostenv env body (get_dummy_frac_term ()) size_first size_all assuming cont
    | CoefAsn (l, coef', body) ->
      evalpat true ghostenv env coef' RealType RealType $. fun ghostenv env coef' ->
      produce_asn_core tpenv h ghostenv env body (real_mul l coef coef') size_first size_all assuming cont
    | WPluginAsn (l, xs, wasn) ->
      let [_, ((_, plugin), symb)] = pluginmap in
      let (pluginState, h) =
        match extract (function Chunk ((p, true), _, _, _, Some (PluginChunkInfo info)) when p == symb -> Some info | _ -> None) h with
          None -> (plugin#empty_state, h)
        | Some (s, h) -> (s, h)
      in
      plugin#produce_assertion pluginState env wasn $. fun pluginState env ->
      cont (Chunk ((symb, true), [], real_unit, [], Some (PluginChunkInfo pluginState))::h) (xs @ ghostenv) env
    )
  in
  let produce_asn tpenv h ghostenv (env: (string * termnode) list) p coef size_first size_all cont =
    produce_asn_core tpenv h ghostenv env p coef size_first size_all false cont
  in
  
  (* Region: consumption of assertions *)
  
  (** Checks if the specified predicate assertion matches the specified chunk. If not, returns None. Otherwise, returns the environment updated with new bindings and other stuff.
      Parameters:
        ghostenv (ghostEnvironment): string list -- The list of all variables that are ghost variables (i.e., not real variables). match_chunk adds all new bindings to this
          list. (Or, more correctly, it returns an updated list obtained by adding all new bindings.
        h (heap): chunk list -- Passed in only so that it can be passed to assert_false when an error is detected.
        env (environment): (string * term) list -- The environment used to evaluate expressions in the predicate assertion, and updated with new bindings.
        env' (environment'): (string * term) list -- The list of bindings of unbound variables. When closing a chunk, the user need not specify values for all arguments.
          As a result, the predicate body gets evaluated with an incomplete environment. This is okay so long as all unspecified (i.e. unbound) parameters appear in
          special positions where VeriFast knows how to derive their value, e.g. in the position of an output argument of a precise predicate assertion.
          match_chunk updates this list with new bindings.
        l (sourceLocation): loc -- The appropriate source location to use when reporting an error
        g (predicateName): (term * bool) -- Predicate name specified in the predicate assertion, against which to compare the predicate name of the chunk
        targs (typeArguments): type_ list -- (For a predicate with type parameters) The type arguments specified in the predicate assertion, possibly further
          instantiated with type variable bindings from the environment of this operation, e.g. from an outer type-parameterized predicate.
        coef (baseCoefficient): term -- A term denoting a real number. The base coefficient with which the coefficient specified in the predicate assertion should
          be multiplied before comparing with the coefficient of the chunk. The base coefficient is typically 1, but can be something else if a coefficient is
          specified in a close statement, e.g. "close [1/2]foo();".
        coefpat (coefficientPattern): pat0 -- Coefficient pattern specified in the predicate assertion
        inputParamCount (inputParameterCount): int option -- In case of a precise predicate, specified the number of input parameters
        pats (argumentPatterns): pat0 list -- Predicate arguments specified in the predicate assertion
        tps0 (semiinstantiatedParameterTypes): type_ list -- Parameter types of the predicate when instantiating its type parameters with the type arguments specified in
          the predicate assertion. Note that these may themselves contain type variables declared by e.g. the predicate that contains the predicate assertion. The
          latter are not instantiated. The predicate argument expressions have been typechecked against these partially-instantiated types. Therefore, the environment
          used to evaluate the predicate arguments must be boxed correctly for these types. (Boxing is necessary because the SMT solvers do not support generics.)
        tps (instantiatedParameterTypes): type_ list -- Parameter types of the predicate, after instantiation with both the type parameter bindings specified in
          the predicate assertion and any additional type parameter bindings from the environment.
        chunk: chunk -- The chunk against which to match the predicate assertion
      Returns:
        None -- no match
        Some (chunk, coef0, ts0, size0, ghostenv, env, env', newChunks)
          chunk: chunk -- The chunk that was matched
          coef0, ts0, size0 -- Coefficient, arguments, size of the chunk that was matched (duplicates stuff from 'chunk')
          ghostenv -- Updated ghost environment
          env -- Updated environment
          env' -- Updated list of bindings of unbound variables
          newChunks -- Any new chunks generated by this match; in particular, auto-splitting of fractional permissions.
   *)
  let match_chunk ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps (Chunk (g', targs0, coef0, ts0, size0) as chunk) =
    let match_pat ghostenv env env' isInputParam pat tp0 tp t cont =
      let match_terms v t =
        if definitely_equal v t then
          cont ghostenv env env'
        else if isInputParam then
          None
        else
          assert_false h env l (Printf.sprintf "Cannot prove %s == %s" (ctxt#pprint t) (ctxt#pprint v)) None
      in
      match (pat, t) with
      | (SrcPat (LitPat (Var (lx, x, scope))), t) when !scope = Some LocalVar ->
        begin match try_assoc x env with
          Some t' -> match_terms (prover_convert_term t' tp0 tp) t
        | None -> let binding = (x, prover_convert_term t tp tp0) in cont ghostenv (binding::env) (binding::env')
        end
      | (SrcPat (LitPat e), t) ->
        match_terms (prover_convert_term (eval None env e) tp0 tp) t
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
      if coef == real_unit && coefpat == real_unit_pat && coef0 == real_unit then cont chunk ghostenv env coef0 [] else
      let match_term_coefpat t =
        let t = real_mul l coef t in
        if definitely_equal t coef0 then
          cont chunk ghostenv env coef0 []
        else
          let half_coef0 = ctxt#mk_real_mul real_half coef0 in
          if definitely_equal t half_coef0 then
            let chunk' = Chunk (g', targs0, half_coef0, ts0, size0) in
            cont chunk' ghostenv env half_coef0 [chunk']
          else if ctxt#query (ctxt#mk_real_lt real_zero t) && ctxt#query (ctxt#mk_real_lt t coef0) then
            cont (Chunk (g', targs0, t, ts0, size0)) ghostenv env t [Chunk (g', targs0, ctxt#mk_real_sub coef0 t, ts0, size0)]
          else
            None
            (*if inputParamCount = None then
              None
            else
              assert_false h env l (Printf.sprintf "Fraction mismatch: cannot prove %s == %s or 0 < %s < %s" (ctxt#pprint t) (ctxt#pprint coef0) (ctxt#pprint t) (ctxt#pprint coef0)) (Some "fractionmismatch")*)
      in
      match coefpat with
        SrcPat (LitPat e) -> match_term_coefpat (eval None env e)
      | TermPat t -> match_term_coefpat t
      | SrcPat (VarPat x) -> cont chunk (x::ghostenv) (update env x (real_div l coef0 coef)) coef0 []
      | SrcPat DummyPat ->
        if is_dummy_frac_term coef0 then
          let dummy' = get_dummy_frac_term () in
          cont (Chunk (g', targs0, dummy', ts0, size0)) ghostenv env dummy' [Chunk (g', targs0, get_dummy_frac_term (), ts0, size0)]
        else
          cont chunk ghostenv env coef0 []
    in
    if not (predname_eq g g' && List.for_all2 unify targs targs0) then None else
    match_pats ghostenv env env' 0 pats tps0 tps ts0 $. fun ghostenv env env' ->
    match_coef ghostenv env $. fun chunk ghostenv env coef0 newChunks ->
    Some (chunk, coef0, ts0, size0, ghostenv, env, env', newChunks)
  in
  
  let lookup_points_to_chunk_core h0 f_symb t =
    let rec iter h =
      match h with
        [] -> None
      | Chunk ((g, true), targs, coef, [t0; v], _)::_ when g == f_symb && definitely_equal t0 t -> Some v
      | Chunk ((g, false), targs, coef, [t0; v], _):: _ when definitely_equal g f_symb && definitely_equal t0 t -> Some v
      | _::h -> iter h
    in
    iter h0
  in

  let lookup_points_to_chunk h0 env l f_symb t =
    match lookup_points_to_chunk_core h0 f_symb t with
      None -> assert_false h0 env l ("No matching pointsto chunk: " ^ (ctxt#pprint f_symb) ^ "(" ^ (ctxt#pprint t) ^ ", _)") None
    | Some v -> v
  in

  let read_field h env l t fparent fname =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
    lookup_points_to_chunk h env l f_symb t
  in
  
  let read_static_field h env l fparent fname =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
    match extract (function Chunk (g, targs, coef, arg0::args, size) when predname_eq (f_symb, true) g -> Some arg0 | _ -> None) h with
      None -> assert_false h env l ("No matching heap chunk: " ^ ctxt#pprint f_symb) None
    | Some (v, _) -> v
  in
  
  let try_read_java_array h env l a i tp =
    head_flatmap
      begin function
        Chunk ((g, true), [tp], coef, [a'; i'; v], _)
          when g == array_element_symb() && definitely_equal a' a && definitely_equal i' i ->
          [v]
      | Chunk ((g, true), [tp], coef, [a'; istart; iend; vs], _)
          when g == array_slice_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) ->
          let (_, _, _, _, nth_symb) = List.assoc "nth" purefuncmap in
          [apply_conversion ProverInductive (provertype_of_type tp) (mk_app nth_symb [ctxt#mk_sub i istart; vs])]
     (* | Chunk ((g, true), [tp;tp2;tp3], coef, [a'; istart; iend; p; info; elems; vs], _)
          when g == array_slice_deep_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) ->
          let (_, _, _, _, nth_symb) = List.assoc "nth" purefuncmap in
          [apply_conversion ProverInductive (provertype_of_type tp) (mk_app nth_symb [ctxt#mk_sub i istart; vs])]*)
      | _ -> []
      end
      h
  in
  
  let try_update_java_array h env l a i tp new_value =
    let rec try_update_java_array_core todo seen = 
      match todo with
        [] -> None
      | Chunk ((g, true), [tp], coef, [a'; i'; v], b) :: rest
          when g == array_element_symb() && definitely_equal a' a && definitely_equal i' i ->
        Some(seen @ ((Chunk ((g, true), [tp], coef, [a'; i'; new_value], b)) :: rest))
      | Chunk ((g, true), [tp], coef, [a'; istart; iend; vs], b) :: rest
          when g == array_slice_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) ->
        let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
        let converted_new_value = apply_conversion (provertype_of_type tp) ProverInductive new_value in
        let updated_vs = (mk_app update_symb [ctxt#mk_sub i istart; converted_new_value; vs]) in
        Some(seen @ ((Chunk ((g, true), [tp], coef, [a'; istart; iend; updated_vs], b)) :: rest))
      | chunk :: rest ->
        try_update_java_array_core rest (seen @ [chunk])
    in
      try_update_java_array_core h [] 
  in
  
  let read_java_array h env l a i tp =
    let slices = try_read_java_array h env l a i tp in
    match slices with
      None -> assert_false h env l "No matching array element or array slice chunk" None
    | Some v -> v
  in
  
  let pointer_pred_symb () =
    let (_, _, _, _, pointer_pred_symb, _) = List.assoc "pointer" predfammap in
    pointer_pred_symb
  in

  let int_pred_symb () =
    let (_, _, _, _, int_pred_symb, _) = List.assoc "integer" predfammap in
    int_pred_symb
  in

  let u_int_pred_symb () =
    let (_, _, _, _, u_int_pred_symb, _) = List.assoc "u_integer" predfammap in
    u_int_pred_symb
  in
  
  let char_pred_symb () =
    let (_, _, _, _, char_pred_symb, _) = List.assoc "character" predfammap in
    char_pred_symb
  in

  let u_char_pred_symb () =
    let (_, _, _, _, u_char_pred_symb, _) = List.assoc "u_character" predfammap in
    u_char_pred_symb
  in
  
  let try_pointee_pred_symb pointeeType =
    match pointeeType with
      PtrType _ -> Some (pointer_pred_symb ())
    | IntType -> Some (int_pred_symb ())
    | UintPtrType -> Some (u_int_pred_symb ())
    | Char -> Some (char_pred_symb ())
    | UChar -> Some (u_char_pred_symb ())
    | _ -> None
  in
  
  let pointee_pred_symb l pointeeType =
    match try_pointee_pred_symb pointeeType with
      Some symb -> symb
    | None -> static_error l ("Dereferencing pointers of type " ^ string_of_type pointeeType ^ " is not yet supported.") None
  in
  
  let read_c_array h env l a i tp =
    let (_, _, _, _, c_array_symb, _) = List.assoc "array" predfammap in
    let predsym = pointee_pred_symb l tp in
    let slices =
      head_flatmap
        begin function
          Chunk (g, [tp2], coef, [a'; n'; size'; q'; vs'], _)
            when predname_eq g (c_array_symb, true) && tp = tp2 && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) i) (ctxt#mk_lt i n')) &&
            ctxt#query (ctxt#mk_eq size' (sizeof l tp)) ->
            let (_, _, _, _, nth_symb) = List.assoc "nth" purefuncmap in
            [apply_conversion ProverInductive (provertype_of_type tp) (mk_app nth_symb [i; vs'])]
        | _ -> []
        end
        h
    in
    match slices with
      None ->
        begin match lookup_points_to_chunk_core h predsym (ctxt#mk_add a (ctxt#mk_mul i (sizeof l tp))) with
          None -> assert_false h env l ("No matching array chunk: array<" ^
                  (string_of_type tp) ^ ">(" ^ (ctxt#pprint a) ^ ", 0<=" ^
                  (ctxt#pprint i) ^ "<n, " ^ (ctxt#pprint (sizeof l tp)) ^
                  ", _, _).") None
        | Some v -> v
        end
    | Some v -> v
  in
  
  let read_array h env l a i tp = 
    match language with 
      Java -> read_java_array h env l a i tp
    | CLang -> read_c_array h env l a i tp
  in
  
  let deref_pointer h env l pointerTerm pointeeType =
    lookup_points_to_chunk h env l (pointee_pred_symb l pointeeType) pointerTerm
  in
  
  let lists_disjoint xs ys =
    List.for_all (fun x -> not (List.mem x ys)) xs
  in
  
  let with_updated_ref r f body =
    let value = !r in
    r := f value;
    do_finally body (fun () -> r := value)
  in
  
  let consume_chunk_recursion_depth = ref 0 in
  
  (** consume_chunk_core attempts to consume a chunk matching the specified predicate assertion from the specified heap.
      If no matching chunk is found in the heap, automation rules are tried (e.g. auto-open and auto-close rules).
      Parameters:
        rules -- The automation rules
        h (heap): chunk list -- The heap
        ghostenv (ghostEnvironment): string list -- The list of ghost variables. Used to check that ghost variables are not used in real code.
        env (environment): (string * term) list -- The environment that binds variable names to their symbolic value. Updated with new bindings.
        env' (unboundVariableBindings): (string * term) list -- Bindings of variables that were declared but not bound. (Happens when you do not specify values for all predicate parameters when closing a chunk.)
        l (sourceLocation): loc -- Appropriate source location to use when reporting an error.
        g (predicateName): (term * bool) -- Predicate name specified in the predicate assertion.
        targs (typeArguments): type_ list -- Type arguments specified in the predicate assertion, instantiated with any type variable bindings currently in effect
        coef (baseCoefficient): term -- Base coefficient in effect. The coefficient specified in the predicate assertion should be multiplied by this base coefficient
          before comparing with a chunk found in the heap. Typically 1, unless e.g. a coefficient is specified in a close statement ('close [1/2]foo();').
        coefpat (coefficientPattern): pat0 -- Coefficient specified in the predicate assertion.
        inputParamCount (inputParameterCount): int option -- If the predicate is precise, specifies the number of input parameters.
        pats (argumentPatterns): pat0 list -- Predicate arguments specified in the predicate assertion.
        tps0 (semiinstantiatedParameterTypes): type_ list -- Predicate parameter types, after instantiation with the type arguments specified in the predicate
          assertion, but without further instantiation. Argument expressions in 'pats' are typechecked against these types and expect that terms are boxed correctly
          with respect to these types.
        tps (instantiatedParameterTypes): type_ list -- Predicate parameter types, after instantiation with the type arguments specified in the predicate assertion,
          as well as any additional type variable bindings currently in effect (e.g. type arguments of an outer predicate, as in 'close foo<int>();').
        cont: continuation called if successful. Typical call:
          [cont chunk h coef ts size ghostenv env env']
            chunk: chunk -- chunk that was consumed (used by the 'leak' command to re-produce all consumed chunks with dummy fraction coefficients)
            h -- heap obtained by removing the consumed chunk (as well as applying any automation rules)
            coef, ts, size -- Coefficient, arguments, size of consumed chunk (duplicates info from 'chunk')
            ghostenv: string list -- Updated ghost environment
            env: (string * term) list -- Updated environment
            env': (string * term) list -- Updated list of bindings of declared but unbound variables
    *)
  let consume_chunk_core rules h ghostenv env env' l g targs coef coefpat inputParamCount pats tps0 tps cont =
    let rec consume_chunk_core_core h =
      let rec iter hprefix h =
        match h with
          [] -> []
        | chunk::h ->
            match match_chunk ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps chunk with
              None -> iter (chunk::hprefix) h
            | Some (chunk, coef, ts, size, ghostenv, env, env', newChunks) -> [(chunk, newChunks @ hprefix @ h, coef, ts, size, ghostenv, env, env')]
      in
      match iter [] h with
        [] ->
        begin fun cont ->
          if !consume_chunk_recursion_depth > 100 then cont () else
          with_updated_ref consume_chunk_recursion_depth ((+) 1) $. fun () ->
          if inputParamCount = None then cont () else
          begin fun cont' ->
            let Some inputParamCount = inputParamCount in
            let rec iter n ts pats tps0 tps =
              if n = 0 then cont' (List.rev ts) else
              match (pats, tps0, tps) with
              | (pat::pats, tp0::tps0, tp::tps) ->
                let ok t = iter (n - 1) (prover_convert_term t tp0 tp::ts) pats tps0 tps in
                match pat with
                  SrcPat (LitPat e) -> ok (eval None env e)
                | TermPat t -> ok t
                | _ -> cont ()
            in
            iter inputParamCount [] pats tps0 tps
          end $. fun ts ->
          match g with
            (g, _) ->
            begin match try_assq g rules with
              Some rules ->
              let terms_are_well_typed = List.for_all (function SrcPat (LitPat (WidenedParameterArgument _)) -> false | _ -> true) pats in
              let rec iter rules =
                match rules with
                  [] -> cont ()
                | rule::rules ->
                  rule h targs terms_are_well_typed ts $. fun h ->
                  match h with
                    None -> iter rules
                  | Some h ->
                    with_context (Executing (h, env, l, "Consuming chunk (retry)")) $. fun () ->
                    consume_chunk_core_core h
              in
              iter rules
            | None -> cont ()
            end
          | _ -> cont ()
        end $. fun () ->
        let message =
          let predname = match g with (g, _) -> ctxt#pprint g in
          let targs =
            match targs with
              [] -> ""
            | _ -> Printf.sprintf "<%s>" (String.concat ", " (List.map string_of_type targs))
          in
          let args =
            let rec iter patvars pats args =
              match pats with
                [] -> List.rev args
              | TermPat t::pats -> iter patvars pats (ctxt#pprint t::args)
              | SrcPat (LitPat (Var (_, x, scope)))::pats when !scope = Some LocalVar -> iter patvars pats ((if List.mem_assoc x env then ctxt#pprint (List.assoc x env) else "_")::args)
              | SrcPat (LitPat e)::pats -> iter patvars pats ((if patvars = [] || lists_disjoint patvars (vars_used e) then ctxt#pprint (eval None env e) else "<expr>")::args)
              | SrcPat DummyPat::pats -> iter patvars pats ("_"::args)
              | SrcPat (VarPat x)::pats -> iter (x::patvars) pats ("_"::args)
            in
            String.concat ", " (iter [] pats [])
          in
          Printf.sprintf "No matching heap chunks: %s%s(%s)" predname targs args
        in
        assert_false h env l message (Some "nomatchingheapchunks")
  (*      
      | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
      | _ -> assert_false h env l "Multiple matching heap chunks." None
  *)
      | (chunk, h, coef, ts, size, ghostenv, env, env')::_ -> cont chunk h coef ts size ghostenv env env'
    in
    consume_chunk_core_core h
  in
  
  (** [cont] is called as [cont chunk h coef ts size ghostenv env env']. See docs at consume_chunk_core. *)
  let consume_chunk rules h ghostenv env env' l g targs coef coefpat inputParamCount pats cont =
    let tps = List.map (fun _ -> IntType) pats in (* dummies, to indicate that no prover type conversions are needed *)
    consume_chunk_core rules h ghostenv env env' l g targs coef coefpat inputParamCount pats tps tps cont
  in
  
  let srcpat pat = SrcPat pat in
  let srcpats pats = List.map srcpat pats in
  
  let rec consume_asn_core rules tpenv h ghostenv env env' p checkDummyFracs coef cont =
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ ->
        if !verbosity >= 2 then Printf.printf "%10.6fs: %s: Consuming assertion\n" (Perf.time()) (string_of_loc (asn_loc p));
        with_context (Executing (h, env, asn_loc p, "Consuming assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval None env in
    let check_dummy_coefpat l coefpat coef =
      if language = CLang && checkDummyFracs then
      match coefpat with
        SrcPat DummyPat -> if not (is_dummy_frac_term coef) then assert_false h env l "Cannot match a non-dummy fraction chunk against a dummy fraction pattern. First leak the chunk using the 'leak' command." None
      | _ -> ()
    in
    let points_to l coefpat e tp rhs =
      match e with
        WRead (lr, e, fparent, fname, frange, fstatic, fvalue, fghost) ->
        let (_, (_, _, _, _, symb, _)) = List.assoc (fparent, fname) field_pred_map in
        let (inputParamCount, pats) =
          if fstatic then
            (Some 0, [rhs])
          else
            (Some 1, [SrcPat (LitPat e); rhs])
        in
        consume_chunk rules h ghostenv env env' l (symb, true) [] coef coefpat inputParamCount pats
          (fun chunk h coef ts size ghostenv env env' -> check_dummy_coefpat l coefpat coef; cont [chunk] h ghostenv env env' size)
      | WReadArray (la, ea, _, ei) ->
        let pats = [SrcPat (LitPat ea); SrcPat (LitPat ei); rhs] in
        consume_chunk rules h ghostenv env env' l (array_element_symb(), true) [tp] coef coefpat (Some 2) pats $.
        fun chunk h coef ts size ghostenv env env' ->
        check_dummy_coefpat l coefpat coef;
        cont [chunk] h ghostenv env env' size
    in
    let pred_asn l coefpat g targs pats0 pats =
      let (g_symb, pats0, pats, types) =
        match try_assoc g#name predfammap with
          Some (_, _, _, _, symb, _) -> ((symb, true), pats0, pats, g#domain)
        | None ->
          begin match try_assoc (g#name) env with
            Some term -> ((term, false), pats0, pats, g#domain)
          | None ->
            let PredCtorInfo (l, ps1, ps2, body, funcsym) = List.assoc g#name predctormap in
            let ctorargs = List.map (function SrcPat (LitPat e) -> ev e | _ -> static_error l "Patterns are not supported in predicate constructor argument positions." None) pats0 in
            let g_symb = mk_app funcsym ctorargs in
            ((g_symb, false), [], pats, List.map snd ps2)
          end
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv types in
      let inputParamCount = match g#inputParamCount with None -> None | Some n -> Some (List.length pats0 + n) in
      consume_chunk_core rules h ghostenv env env' l g_symb targs coef coefpat inputParamCount (pats0 @ pats) types domain (fun chunk h coef ts size ghostenv env env' ->
        check_dummy_coefpat l coefpat coef;
        cont [chunk] h ghostenv env env' size
      )
    in
    let inst_call_pred l coefpat e_opt tn g index pats =
      let (pmap, pred_symb) =
        match try_assoc tn classmap1 with
          Some (lcn, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
          let (_, pmap, _, symb, _) = List.assoc g preds in (pmap, symb)
        | None ->
          match try_assoc tn classmap0 with
            Some {cpreds} ->
            let (_, pmap, _, symb, _) = List.assoc g cpreds in (pmap, symb)
          | None ->
            match try_assoc tn interfmap1 with
              Some (li, fields, methods, preds, interfs, pn, ilist) -> let (_, pmap, family, symb) = List.assoc g preds in (pmap, symb)
            | None ->
              let InterfaceInfo (li, fields, methods, preds, interfs) = List.assoc tn interfmap0 in
              let (_, pmap, family, symb) = List.assoc g preds in
              (pmap, symb)
      in
      let target = match e_opt with None -> List.assoc "this" env | Some e -> ev e in
      let index = ev index in
      let types = ObjType tn::ObjType "java.lang.Class"::List.map snd pmap in
      let pats = TermPat target::TermPat index::srcpats pats in
      consume_chunk_core rules h ghostenv env env' l (pred_symb, true) [] coef coefpat (Some 2) pats types types $. fun chunk h coef ts size ghostenv env env' ->
      check_dummy_coefpat l coefpat coef;
      cont [chunk] h ghostenv env env' size
    in
    match p with
    | WPointsTo (l, e, tp, rhs) -> points_to l real_unit_pat e tp (SrcPat rhs)
    | WPredAsn (l, g, _, targs, pats0, pats) -> pred_asn l real_unit_pat g targs (srcpats pats0) (srcpats pats)
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
      inst_call_pred l real_unit_pat e_opt tn g index pats
    | ExprAsn (l, Operation (lo, Eq, [Var (lx, x, scope); e], tps)) when !scope = Some LocalVar ->
      begin match try_assoc x env with
        Some t -> assert_term (ctxt#mk_eq t (ev e)) h env l "Cannot prove condition." None; cont [] h ghostenv env env' None
      | None -> let binding = (x, ev e) in cont [] h ghostenv (binding::env) (binding::env') None
      end
   (* | ExprAsn(l, Operation(lo, And, [e1; e2], tps)) ->
      consume_asn_core rules tpenv h ghostenv env env' (ExprAsn (expr_loc e1, e1)) checkDummyFracs coef (fun chunks h ghostenv env env' size ->
        consume_asn_core rules tpenv h ghostenv env env' (ExprAsn (expr_loc e2, e2)) checkDummyFracs coef (fun chunks' h ghostenv env env' _ ->
          cont (chunks @ chunks') h ghostenv env env' size
        )
      )
    | ExprAsn(l, IfExpr(lo, con, e1, e2)) ->
      let cont chunks h _ _ env'' _ = cont chunks h ghostenv (env'' @ env) (env'' @ env') None in
      let env' = [] in
      branch
        (fun _ ->
           assume (ev con) (fun _ ->
             consume_asn_core rules tpenv h ghostenv env env' (ExprAsn (expr_loc e1, e1)) checkDummyFracs coef cont))
        (fun _ ->
           assume (ctxt#mk_not (ev con)) (fun _ ->
             consume_asn_core rules tpenv h ghostenv env env' (ExprAsn (expr_loc e2, e2)) checkDummyFracs coef cont))*)
    | ExprAsn (l, e) ->
      assert_expr env e h env l "Cannot prove condition." None; cont [] h ghostenv env env' None
    | Sep (l, p1, p2) ->
      consume_asn_core rules tpenv h ghostenv env env' p1 checkDummyFracs coef (fun chunks h ghostenv env env' size ->
        consume_asn_core rules tpenv h ghostenv env env' p2 checkDummyFracs coef (fun chunks' h ghostenv env env' _ ->
          cont (chunks @ chunks') h ghostenv env env' size
        )
      )
    | IfAsn (l, e, p1, p2) ->
      let cont chunks h _ _ env'' _ = cont chunks h ghostenv (env'' @ env) (env'' @ env') None in
      let env' = [] in
      branch
        (fun _ ->
           assume (ev e) (fun _ ->
             consume_asn_core rules tpenv h ghostenv env env' p1 checkDummyFracs coef cont))
        (fun _ ->
           assume (ctxt#mk_not (ev e)) (fun _ ->
             consume_asn_core rules tpenv h ghostenv env env' p2 checkDummyFracs coef cont))
    | WSwitchAsn (l, e, i, cs) ->
      let cont chunks h _ _ env'' _ = cont chunks h ghostenv (env'' @ env) (env'' @ env') None in
      let env' = [] in
      let t = ev e in
      let (_, tparams, ctormap, _) = List.assoc i inductivemap in
      let rec iter cs =
        match cs with
          SwitchAsnClause (lc, cn, pats, patsInfo, p)::cs ->
          let (_, (_, tparams, _, tps, ctorsym)) = List.assoc cn ctormap in
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
            (fun _ -> assume_eq t (mk_app ctorsym xs) (fun _ -> consume_asn_core rules tpenv h (pats @ ghostenv) (xenv @ env) env' p checkDummyFracs coef cont))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpAsn l -> cont [] h ghostenv env env' None
    | CoefAsn (l, coefpat, WPointsTo (_, e, tp, rhs)) -> points_to l (SrcPat coefpat) e tp (SrcPat rhs)
    | CoefAsn (l, coefpat, WPredAsn (_, g, _, targs, pat0, pats)) -> pred_asn l (SrcPat coefpat) g targs (srcpats pat0) (srcpats pats)
    | CoefAsn (l, coefpat, WInstPredAsn (_, e_opt, st, cfin, tn, g, index, pats)) -> inst_call_pred l (SrcPat coefpat) e_opt tn g index pats
    | WPluginAsn (l, xs, wasn) ->
      let [_, ((_, plugin), symb)] = pluginmap in
      let (pluginState, h) =
        match extract (function Chunk ((p, true), _, _, _, Some (PluginChunkInfo info)) when p == symb -> Some info | _ -> None) h with
          None -> (plugin#empty_state, h)
        | Some (s, h) -> (s, h)
      in
      try 
        plugin#consume_assertion pluginState env wasn $. fun pluginState env ->
        cont [] (Chunk ((symb, true), [], real_unit, [], Some (PluginChunkInfo pluginState))::h) (xs @ ghostenv) env env' None
      with Plugins.PluginConsumeError (off, len, msg) ->
        let ((path, line, col), _) = l in
        let l = ((path, line, col + 1 + off), (path, line, col + 1 + off + len)) in
        assert_false h env l msg None
    )
  in
  
  let consume_asn rules tpenv h ghostenv env p checkDummyFracs coef cont =
    consume_asn_core rules tpenv h ghostenv env [] p checkDummyFracs coef (fun chunks h ghostenv env env' size_first -> cont chunks h ghostenv env size_first)
  in

  let term_of_pred_index =
    match language with
      Java -> fun cn -> List.assoc cn classterms
    | CLang -> fun fn -> List.assoc fn funcnameterms
  in
  
  let predinstmap_by_predfamsymb =
    flatmap
      begin fun ((p, fns), (env, l, predinst_tparams, xs, symb, inputParamCount, wbody)) ->
        if fns = [] && predinst_tparams = [] && env = [] then
          [(symb, (xs, wbody))]
        else
          []
      end
      predinstmap
  in
  
  (* Those predicate instances that, under certain conditions on the input parameters, are likely to be closeable. *)
  let empty_preds =
    flatmap
      begin fun (((p, fns), (env, l, predinst_tparams, xs, symb, inputParamCount, wbody)) as predinst) ->
        let fsymbs = List.map term_of_pred_index fns in
        match inputParamCount with
          None -> []
        | Some n ->
          let inputVars = List.map fst (take n xs) in
          let rec iter conds wbody cont =
            match wbody with
            | Sep (_, asn1, asn2) ->
              iter conds asn1 (fun conds -> iter conds asn2 cont)
            | IfAsn (_, cond, asn1, asn2) ->
              if expr_is_fixed inputVars cond then
                iter (cond::conds) asn1 cont @ iter (Operation (dummy_loc, Not, [cond], ref None)::conds) asn2 cont
              else
                []
            | ExprAsn (_, Operation (_, Eq, [Var (_, x, _); e], _)) when not (List.mem x inputVars) && expr_is_fixed inputVars e ->
              cont conds
            | ExprAsn (_, e) when expr_is_fixed inputVars e ->
              cont (e::conds)
            | EmpAsn _ -> cont conds
            | WSwitchAsn(_, e, i, cases) when expr_is_fixed inputVars e ->
              flatmap 
                (fun (SwitchAsnClause (l, casename, args, boxinginfo, asn)) ->
                  if (List.length args) = 0 then
                    let cond = Operation (l, Eq, [e; Var (l, casename, ref (Some PureCtor))], ref (Some [AnyType; AnyType])) in
                    iter (cond :: conds) asn cont
                  else 
                   []
                )
                cases
            | _ -> []
          in
          let conds = iter [] wbody (fun conds -> [conds]) in
          if conds <> [] then [(symb, fsymbs, conds, predinst)] else []
      end
      predinstmap
  in
  
  (*let _ =
    begin print_endline "empty predicates:";
    List.iter
      (fun (from_symb, from_indices, conditions_list, _) ->
        begin 
          print_endline (ctxt#pprint from_symb);
          List.iter (fun conds -> 
            print_endline (string_of_int (List.length conds));
            (*List.iter (fun con -> print_endline ("    " ^ (ctxt#pprint con))) conds;*)
            print_endline "  or";
          ) 
          conditions_list;
        end
      )
      empty_preds
    end
  in*)
  
  (* direct edges from a precise predicate or predicate family to other precise predicates 
     - each element of path is of the form:
       (outer_l, outer_symb, outer_is_inst_pred, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_target_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds)
  *)
  let pred_fam_contains_edges =
    flatmap
      (fun (((p, fns), (env, l, predinst_tparams, xs, psymb, inputParamCount, wbody0)) as predinst) ->
        let pindices = List.map term_of_pred_index fns in
        match inputParamCount with
          None -> [] (* predicate is not precise *)
        | Some nbInputParameters ->
          let inputParameters = List.map fst (take nbInputParameters xs) in
          let inputFormals = (take nbInputParameters xs) in
          let rec iter coef conds wbody =
            match wbody with
              WPointsTo(_, WRead(lr, e, fparent, fname, frange, fstatic, fvalue, fghost), tp, v) ->
              if expr_is_fixed inputParameters e || fstatic then
                let (_, (_, _, _, _, qsymb, _)) = List.assoc (fparent, fname) field_pred_map in
                [(psymb, pindices, qsymb, [(l, (psymb, true), false, predinst_tparams, fns, xs, inputFormals, wbody0, coef, None, [], [], (if fstatic then [] else [e]), conds)])]
              else
                []
            | WPredAsn(_, q, true, qtargs, qfns, qpats) ->
              begin match try_assoc q#name xs with
                Some _ -> []
              | None ->
                begin match try_assoc q#name predfammap with
                  None -> [] (* can this happen? *)
                | Some (_, qtparams, _, qtps, qsymb, _) ->
                  begin match q#inputParamCount with
                    None -> [] (* predicate is not precise, can this happen in a precise predicate? *)
                  | Some qInputParamCount ->
                    let qIndices = List.map (fun (LitPat e) -> e) qfns in
                    let qInputActuals = List.map (fun (LitPat e) -> e) (take qInputParamCount qpats) in
                    if List.for_all (fun e -> expr_is_fixed inputParameters e) (qIndices @ qInputActuals) then
                      [(psymb, pindices, qsymb, [(l, (psymb, true), false, predinst_tparams, fns, xs, inputFormals, wbody0, coef, None, qtargs, qIndices, qInputActuals, conds)])]
                    else
                      []
                  end
                end
              end
            | WInstPredAsn(l2, target_opt, static_type_name, static_type_finality, family_type_string, instance_pred_name, index, args) ->
              let (pmap, qsymb) =
                match try_assoc static_type_name classmap1 with
                  Some (lcn, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
                  let (_, pmap, _, symb, _) = List.assoc instance_pred_name preds in (pmap, symb)
                | None ->
                  match try_assoc static_type_name classmap0 with
                    Some {cpreds} ->
                    let (_, pmap, _, symb, _) = List.assoc instance_pred_name cpreds in (pmap, symb)
                  | None ->
                    match try_assoc static_type_name interfmap1 with
                      Some (li, fields, methods, preds, interfs, pn, ilist) -> let (_, pmap, family, symb) = List.assoc instance_pred_name preds in (pmap, symb)
                    | None ->
                      let InterfaceInfo (li, fields, methods, preds, interfs) = List.assoc static_type_name interfmap0 in
                      let (_, pmap, family, symb) = List.assoc instance_pred_name preds in
                      (pmap, symb)
              in
              if match target_opt with Some e -> expr_is_fixed inputParameters e | None -> true then begin
                let target = match target_opt with Some e -> Some e | None -> Some (Var(l2, "this", ref (Some LocalVar))) in
                [(psymb, pindices, qsymb, [(l, (psymb, true), false, predinst_tparams, fns, xs, inputFormals, wbody0, coef, target, [], [index], [], conds)])]
              end else
                []
            | CoefAsn(_, DummyPat, asn) ->
              iter (Some DummyPat) conds asn
            | CoefAsn(_, LitPat(frac), asn) when expr_is_fixed inputParameters frac -> (* extend to arbitrary fractions? *)
              let new_coef = 
                match coef with
                  None -> Some (LitPat frac)
                | Some DummyPat -> Some DummyPat
                | Some (LitPat coef) -> Some (LitPat (Operation(dummy_loc, Mul, [frac;coef], ref (Some [RealType; RealType]))))
              in
              iter new_coef conds asn
            | Sep(_, asn1, asn2) ->
              (iter coef conds asn1) @ (iter coef conds asn2)
            | IfAsn(_, cond, asn1, asn2) ->
              if expr_is_fixed inputParameters cond then
                (iter coef (cond :: conds) asn1) @ (iter coef (Operation(dummy_loc, Not, [cond], ref None) :: conds) asn2)
              else
                (iter coef conds asn1) @ (iter coef conds asn2) (* replace this with []? *)
            | _ -> []
          in
          iter None [] wbody0
      )
      predinstmap
  in
   
  let instance_predicate_contains_edges = 
    classmap1 |> flatmap 
      (fun (cn, (l, abstract, fin, meths, fds, cmap, super, interfs, preds, pn, ilist)) ->
        preds |> flatmap
          (fun ((g, (l, pmap, family, psymb, wbody_opt)) as instance_predicate) ->
            match wbody_opt with None -> [] | Some wbody0 ->
            let pindices = [(List.assoc cn classterms)] in
            let instpred_tparams = [] in
            let fns = [cn] in
            let xs = pmap in
            let inputParameters = ["this"] in
            let inputFormals = [] in
            let rec iter coef conds wbody =
              match wbody with
                WPointsTo(_, WRead(lr, e, fparent, fname, frange, fstatic, fvalue, fghost), tp, v) ->
                if expr_is_fixed inputParameters e || fstatic then
                  let (_, (_, _, _, _, qsymb, _)) = List.assoc (fparent, fname) field_pred_map in
                  [(psymb, pindices, qsymb, [(l, (psymb, true), true, instpred_tparams, fns, xs, inputFormals, wbody0, coef, None, [], [], (if fstatic then [] else [e]), conds)])]
                else
                  []
              | WPredAsn(_, q, true, qtargs, qfns, qpats) ->
                begin match try_assoc q#name xs with
                  Some _ -> []
                | None ->
                  begin match try_assoc q#name predfammap with
                    None -> [] (* can this happen? *)
                  | Some (_, qtparams, _, qtps, qsymb, _) ->
                    begin match q#inputParamCount with
                      None -> [] (* predicate is not precise, can this happen in a precise predicate? *)
                    | Some qInputParamCount ->
                      let qIndices = List.map (fun (LitPat e) -> e) qfns in
                      let qInputActuals = List.map (fun (LitPat e) -> e) (take qInputParamCount qpats) in
                      if List.for_all (fun e -> expr_is_fixed inputParameters e) (qIndices @ qInputActuals) then
                        [(psymb, pindices, qsymb, [(l, (psymb, true), true, instpred_tparams, fns, xs, inputFormals, wbody0, coef, None, qtargs, qIndices, qInputActuals, conds)])]
                      else
                        []
                    end
                  end
                end
              | WInstPredAsn(l2, target_opt, static_type_name, static_type_finality, family_type_string, instance_pred_name, index, args) ->
                let (pmap, qsymb) =
                  match try_assoc static_type_name classmap1 with
                    Some (lcn, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
                    let (_, pmap, _, symb, _) = List.assoc instance_pred_name preds in (pmap, symb)
                  | None ->
                    match try_assoc static_type_name classmap0 with
                      Some {cpreds} ->
                      let (_, pmap, _, symb, _) = List.assoc instance_pred_name cpreds in (pmap, symb)
                    | None ->
                      match try_assoc static_type_name interfmap1 with
                        Some (li, fields, methods, preds, interfs, pn, ilist) -> let (_, pmap, family, symb) = List.assoc instance_pred_name preds in (pmap, symb)
                      | None ->
                        let InterfaceInfo (li, fields, methods, preds, interfs) = List.assoc static_type_name interfmap0 in
                        let (_, pmap, family, symb) = List.assoc instance_pred_name preds in
                        (pmap, symb)
                in
                if match target_opt with Some e -> expr_is_fixed inputParameters e | None -> true then begin
                  let target = match target_opt with Some e -> Some e | None -> Some (Var(l2, "this", ref (Some LocalVar))) in
                  [(psymb, pindices, qsymb, [(l, (psymb, true), true, instpred_tparams, fns, xs, inputFormals, wbody0, coef, target, [], [index], [], conds)])]
                end else
                  []
              | CoefAsn(_, DummyPat, asn) ->
                iter (Some DummyPat) conds asn
              | CoefAsn(_, LitPat(frac), asn) when expr_is_fixed inputParameters frac -> (* extend to arbitrary fractions? *)
                let new_coef = 
                  match coef with
                    None -> Some (LitPat frac)
                  | Some DummyPat -> Some DummyPat
                  | Some (LitPat coef) -> Some (LitPat (Operation(dummy_loc, Mul, [frac;coef], ref (Some [RealType; RealType]))))
                in
                iter new_coef conds asn
              | Sep(_, asn1, asn2) ->
                (iter coef conds asn1) @ (iter coef conds asn2)
              | IfAsn(_, cond, asn1, asn2) ->
                if expr_is_fixed inputParameters cond then
                  (iter coef (cond :: conds) asn1) @ (iter coef (Operation(dummy_loc, Not, [cond], ref None) :: conds) asn2)
                else
                  (iter coef conds asn1) @ (iter coef conds asn2) (* replace this with []? *)
              | _ -> []
            in
            iter None [] wbody0
          )
      )
  in
  
  let contains_edges = pred_fam_contains_edges @ instance_predicate_contains_edges in
  
  let close1_ edges =
    flatmap
    (fun ((from_symb, from_indices, to_symb, path) as edge0) ->
      flatmap 
        (fun ((from_symb0, from_indices0, to_symb0, (((outer_l0, outer_symb0, outer_is_inst_pred0, outer_formal_targs0, outer_actual_indices0, outer_formal_args0, outer_formal_input_args0, outer_wbody0, inner_frac_expr_opt0, inner_target_opt0, inner_formal_targs0, inner_formal_indices0, inner_input_exprs0, conds0) :: rest) as path0)) as edge1) ->
          if to_symb == from_symb0 then
            let rec add_extra_conditions path = 
              match path with
                [(outer_l, outer_symb, outer_is_inst_pred, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_target_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds)] ->
                let extra_conditions: expr list = List.map2 (fun cn e2 -> 
                    if language = Java then 
                      Operation(dummy_loc, Eq, [ClassLit(dummy_loc, cn); e2], ref (Some [ObjType "java.lang.Class"; ObjType "java.lang.Class"]))
                    else 
                      Operation(dummy_loc, Eq, [Var(dummy_loc, cn, ref (Some FuncName)); e2], ref (Some [PtrType Void; PtrType Void]))
                ) outer_actual_indices0 inner_formal_indices in
                (* these extra conditions ensure that the actual indices match the expected ones *)
                [(outer_l, outer_symb, outer_is_inst_pred, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_target_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, extra_conditions @ conds)]
                 
              | head :: rest -> head :: (add_extra_conditions rest)
            in
            let new_path = add_extra_conditions path in
            let new_edge = (from_symb, from_indices, to_symb0, new_path @ path0) in
            if List.exists (fun (from_symb1, from_indices1, to_symb1, _) -> 
                 from_symb1 == from_symb && 
                 (for_all2 (fun t1 t2 -> t1 == t2) from_indices from_indices1) && 
                 to_symb1 == to_symb0) edges then
              []
              (* todo: improve by taking path into account *)
              (* todo: avoid cycles in the path? *)
              (* todo: avoid duplicate entries? *)
            else 
              [new_edge]
          else
            []
        )
        edges
    )
    edges
  in
  
  let transitive_contains_edges_ = 
    let rec close edges =
      let new_edges = close1_ edges in
      if new_edges = [] then
        edges
      else
        close (new_edges @ edges)
    in
    close contains_edges
  in
  
  (*let _ =
    print_endline "transitive_edges:";
    List.iter
      (fun (from_symb, from_indices, to_symb, path) ->
        print_endline ((ctxt#pprint from_symb) ^ " -> " ^ (ctxt#pprint to_symb));
      )
    contains_edges
  in*)
  
  let rules_cell = ref [] in (* A hack to allow the rules to recursively use the rules *)
  
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
    (* transitive auto-close rules for precise predicates and predicate families *)
    List.iter
      (fun (from_symb, indices, to_symb, path) ->
        let transitive_auto_close_rule h wanted_targs terms_are_well_typed wanted_indices_and_input_ts cont =
          let rec can_apply_rule current_this_opt current_targs current_indices current_input_args path =
            match path with
              [] -> 
                begin match try_find
                  (fun (Chunk (found_symb, found_targs, found_coef, found_ts, _)) ->
                    predname_eq found_symb (to_symb, true) &&
                    (let expected_ts = (match current_this_opt with None -> [] | Some t -> [t]) @ current_indices @ current_input_args in
                    (for_all2 definitely_equal (take (List.length (expected_ts)) found_ts) expected_ts))
                  )
                  h
                with
                  None -> begin (* check whether the wanted predicate is an empty predicate? *)
                    if List.exists 
                         (fun (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) ->
                           to_symb == symb &&
                           (for_all2 definitely_equal fsymbs current_indices) &&
                           (
                             let Some inputParamCount = inputParamCount in
                             let Some tpenv = zip predinst_tparams current_targs in
                             let env = List.map2 (fun (x, tp0) actual -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term actual tp tp0)) (take inputParamCount xs) current_input_args in 
                             let env = match current_this_opt with None -> env | Some t -> ("this", t) :: env in
                             List.exists (fun conds -> (List.for_all (fun cond -> ctxt#query (eval None env cond)) conds)) conds
                           )
                         )
                        empty_preds 
                    then
                      Some (fun h cont -> cont h real_unit)
                    else
                      None
                  end
                | Some (Chunk (found_symb, found_targs, found_coef, found_ts, _)) -> Some (fun h cont -> cont h found_coef)
                end
            | (outer_l, outer_symb, outer_is_inst_pred, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_target_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds) :: path ->
              let (outer_s, _) = outer_symb in
              let Some tpenv = zip outer_formal_targs current_targs in
              let env = List.map2 (fun (x, tp0) actual -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term actual tp tp0)) outer_formal_input_args current_input_args in
              let env = match current_this_opt with
                None -> env
              | Some t ->  ("this", t) :: env
              in
              if (List.for_all (fun cond -> ctxt#query (eval None env cond)) conds) then
                let env = List.map2 (fun (x, tp0) actual -> (x, actual)) outer_formal_input_args current_input_args in
                let env = match current_this_opt with
                  None -> env
                | Some t -> ("this", t) :: env
                in
                let new_this_opt = match inner_target_opt with
                  None -> None
                | Some thisExpr -> Some (eval None env thisExpr)
                in 
                let new_actual_targs = List.map (fun tp0 -> (instantiate_type tpenv tp0)) inner_formal_targs in
                let new_actual_indices = List.map (fun index -> (eval None env index)) inner_formal_indices in
                let new_actual_input_args = List.map (fun input_e -> (eval None env input_e)) inner_input_exprs in
                match can_apply_rule new_this_opt new_actual_targs new_actual_indices new_actual_input_args path with
                  None -> None
                | Some exec_rule -> Some (fun h cont ->
                    exec_rule h (fun h coef ->
                      let rules = ! rules_cell in
                      let ghostenv = [] in
                      let checkDummyFracs = true in
                      let env = List.map2 (fun (x, tp0) actual -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term actual tp tp0)) outer_formal_input_args current_input_args in
                      let env = match current_this_opt with
                        None -> env
                      | Some t -> ("this", t) :: env
                      in
                      with_context (Executing (h, env, outer_l, "Auto-closing predicate")) $. fun () ->
                        let new_coef = 
                          match inner_frac_expr_opt with
                            None -> coef
                          | Some DummyPat -> real_unit
                          | Some (LitPat (RealLit(_, n))) -> ctxt#mk_real_mul coef (ctxt#mk_reallit_of_num ((num_of_big_int unit_big_int) // n))
                          | Some _ -> coef (* todo *)
                        in
                        consume_asn rules tpenv h ghostenv env outer_wbody checkDummyFracs new_coef $. fun _ h ghostenv env2 size_first ->
                          let outputParams = drop (List.length outer_formal_input_args) outer_formal_args in
                          let outputArgs = List.map (fun (x, tp0) -> let tp = instantiate_type tpenv tp0 in (prover_convert_term (List.assoc x env2) tp0 tp)) outputParams in
                          with_context (Executing (h, [], outer_l, "Producing auto-closed chunk")) $. fun () ->
                            let input_param_count = match current_this_opt with Some _ -> Some 2 | None -> Some((List.length current_indices) + (List.length current_input_args)) in
                            produce_chunk h outer_symb current_targs new_coef input_param_count ((match current_this_opt with None -> [] | Some t -> [t]) @ current_indices @ current_input_args @ outputArgs) None (fun h -> 
                            cont h new_coef) (* todo: properly set the size *)
                    )
                  )
              else 
                None (* conditions do not hold, so give up *)
          in
          let wanted_indices = match List.hd path with
            (_, _, true, _, _, _, _, _, _, _, _, _, _, _) -> 
             (take (List.length indices) (List.tl wanted_indices_and_input_ts))
          | (_, _, false, _, _, _, _, _, _, _, _, _, _, _) -> 
             (take (List.length indices) wanted_indices_and_input_ts)
          in
          if terms_are_well_typed &&
             (for_all2 definitely_equal indices wanted_indices) (* check that you are actually looking for from_symb at indices *) then
            let (wanted_target_opt, wanted_indices, wanted_inputs) = 
              match List.hd path with
                  (_, _, true, _, _, _, _, _, _, _, _, _, _, _) -> 
                  (Some (List.hd wanted_indices_and_input_ts), (take (List.length indices) (List.tl wanted_indices_and_input_ts)),
                  (drop (List.length indices) (List.tl wanted_indices_and_input_ts)))
                | (_, _, false, _, _, _, _, _, _, _, _, _, _, _) -> 
                  (None, (take (List.length indices) wanted_indices_and_input_ts), (drop (List.length indices) wanted_indices_and_input_ts))
            in
            match can_apply_rule wanted_target_opt wanted_targs wanted_indices wanted_inputs path with
              None -> cont None
            | Some exec_rule -> exec_rule h (fun h _ -> cont (Some h))
          else
            cont None
        in
        add_rule from_symb transitive_auto_close_rule
      )
      transitive_contains_edges_;
    (* transitive auto-open rules for precise predicates and predicate families *)
    List.iter 
      (fun (from_symb, indices, to_symb, path) ->
        let transitive_auto_open_rule h wanted_targs terms_are_well_typed wanted_indices_and_input_ts cont =
          let rec try_apply_rule_core actual_this_opt actual_targs actual_indices actual_input_args path = 
            match path with
            | [] ->
              if for_all2 definitely_equal wanted_indices_and_input_ts ((match actual_this_opt with None -> [] | Some t -> [t]) @ actual_indices @ actual_input_args) then
                Some (fun h_opt cont -> begin match h_opt with None -> cont None | Some(h) -> cont (Some h) end)
              else
                None
            | (outer_l, outer_symb, outer_is_inst_pred, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_target_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds) :: path ->
              
              let (outer_s, _) = outer_symb in
              let actual_input_args = (take (List.length outer_formal_input_args) actual_input_args) in (* to fix first call *)
              let Some tpenv = zip outer_formal_targs actual_targs in
              let env = List.map2 (fun (x, tp0) actual -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term actual tp tp0)) outer_formal_input_args actual_input_args in
              let env = match actual_this_opt with
                  None -> env
                | Some t -> ("this", t) :: env
              in
              if (List.for_all (fun cond -> ctxt#query (eval None env cond)) conds) then
                let env = List.map2 (fun (x, tp0) actual -> (x, actual)) outer_formal_input_args actual_input_args in
                let env = match actual_this_opt with
                  None -> env
                | Some t -> ("this", t) :: env
                in
                let new_this_opt = match inner_target_opt with
                  None -> None
                | Some thisExpr -> Some (eval None env thisExpr)
                in
                let new_actual_targs = List.map (fun tp0 -> (instantiate_type tpenv tp0)) inner_formal_targs in
                let new_actual_indices = List.map (fun index -> (eval None env index)) inner_formal_indices in
                let new_actual_input_args = List.map (fun input_e -> (eval None env input_e)) inner_input_exprs in
                match try_apply_rule_core new_this_opt new_actual_targs new_actual_indices new_actual_input_args path with
                  None -> None
                | Some(exec_rule) ->
                  Some (fun h_opt cont ->
                    begin match h_opt with
                      None -> cont None
                    | Some h ->
                      (* consume from_symb *)
                      let result_opt =
                        let rec iter hdone htodo =
                          match htodo with
                            [] -> None (* todo: can happen if predicate is only present under conditions that contain non-input variables *)
                          | (Chunk (found_symb, found_targs, found_coef, found_ts, _) as chunk)::htodo ->
                            if (predname_eq outer_symb found_symb) && 
                               (let actuals = ((match actual_this_opt with None -> [] | Some t -> [t]) @ actual_indices @ actual_input_args) in
                               (for_all2 definitely_equal (take (List.length actuals) found_ts)) actuals) then
                               Some ((hdone @ htodo, found_targs, found_coef, found_ts))
                            else
                              iter (chunk::hdone) htodo
                        in
                        iter [] h
                      in
                      begin match result_opt with
                        None -> cont None
                      | Some ((h, found_targs, found_coef, found_ts)) -> 
                        (* produce from_symb body *)
                        let full_env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) outer_formal_args (drop ((List.length actual_indices) + (match actual_this_opt with None -> 0 | Some _ -> 1)) found_ts) in 
                        let full_env = match actual_this_opt with None -> full_env | Some t -> ("this", t) :: full_env in
                        let ghostenv = [] in
                        with_context (Executing (h, full_env, outer_l, "Auto-opening predicate")) $. fun () ->
                          produce_asn tpenv h ghostenv full_env outer_wbody found_coef None None $. fun h ghostenv env ->
                            (* perform remaining opens *)
                            exec_rule (Some h) cont
                      end
                    end
                  )
              else
                None
          in
          let try_apply_rule hdone htodo =
            let rec try_apply_rule0 hdone htodo = 
              match htodo with
                [] -> None
              | ((Chunk (actual_name, actual_targs, actual_coef, actual_ts, _)) as chnk) :: rest 
                  when (predname_eq actual_name (from_symb, true)) && (
                       let indices0 = match List.hd path with
                         (_, _, true, _, _, _, _, _, _, _, _, _, _, _) ->  (take (List.length indices) (List.tl actual_ts))
                       | (_, _, false, _, _, _, _, _, _, _, _, _, _, _) -> (take (List.length indices) actual_ts)
                       in
                        (for_all2 definitely_equal indices0 indices)
                       ) ->
                let (actual_target_opt, actual_indices, actual_inputs) = 
                  match List.hd path with
                    (_, _, true, _, _, _, _, _, _, _, _, _, _, _) ->  (Some (List.hd actual_ts), indices, (drop (List.length indices) (List.tl actual_ts)))
                  | (_, _, false, _, _, _, _, _, _, _, _, _, _, _) -> (None, indices, (drop (List.length indices) actual_ts))
                in
                begin match try_apply_rule_core actual_target_opt actual_targs actual_indices actual_inputs path with
                  None -> try_apply_rule0 (chnk :: hdone) rest
                | Some exec_rule -> Some exec_rule
                end
              | chnk :: rest -> try_apply_rule0 (chnk :: hdone) rest
            in
            try_apply_rule0 hdone htodo
          in
          if terms_are_well_typed then
            match try_apply_rule [] h with
              None -> cont None
            | Some exec_rule -> exec_rule (Some h) cont
          else
            cont None
         in
         add_rule to_symb transitive_auto_open_rule;
      )
      transitive_contains_edges_;
    (* rules for closing empty chunks *)
    List.iter
      begin fun (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) ->
        let g = (symb, true) in
        let indexCount = List.length fns in
        let Some n = inputParamCount in
        let (inputParams, outputParams) = take_drop n xs in
        let autoclose_rule =
          let match_func h targs ts =
            let (indices, inputArgs) = take_drop indexCount ts in
            List.for_all2 definitely_equal indices fsymbs &&
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
            List.exists (fun conds -> List.for_all (fun cond -> ctxt#query (eval None env cond)) conds) conds
          in
          let exec_func h targs ts cont =
            let rules = !rules_cell in
            let (indices, inputArgs) = take_drop indexCount ts in
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
            let ghostenv = [] in
            let checkDummyFracs = true in
            let coef = real_unit in
            with_context (Executing (h, env, l, "Auto-closing predicate")) $. fun () ->
            consume_asn rules tpenv h ghostenv env wbody checkDummyFracs coef $. fun _ h ghostenv env size_first ->
            let outputArgs = List.map (fun (x, tp0) -> let tp = instantiate_type tpenv tp0 in (prover_convert_term (List.assoc x env) tp0 tp)) outputParams in
            with_context (Executing (h, [], l, "Producing auto-closed chunk")) $. fun () ->
            cont (Chunk (g, targs, coef, inputArgs @ outputArgs, None)::h)
          in
          let rule h targs terms_are_well_typed ts cont =
            if terms_are_well_typed && match_func h targs ts then exec_func h targs ts (fun h -> cont (Some h)) else cont None
          in
          rule
        in
        add_rule symb autoclose_rule
      end
      empty_preds;
    (* rules for array slices *)
    begin if language = Java then
      let array_element_symb = array_element_symb () in
      let array_slice_symb = array_slice_symb () in
      let array_slice_deep_symb = array_slice_deep_symb () in
      let get_element_rule h [elem_tp] terms_are_well_typed [arr; index] cont =
        match extract
          begin function
            (Chunk ((g, is_symb), elem_tp'::targs_rest, coef, arr'::istart'::iend'::args_rest, _)) when
              (g == array_slice_symb || g == array_slice_deep_symb) &&
              definitely_equal arr' arr && ctxt#query (ctxt#mk_and (ctxt#mk_le istart' index) (ctxt#mk_lt index iend')) &&
              unify elem_tp elem_tp' ->
            Some (g, targs_rest, coef, istart', iend', args_rest)
          | _ -> None
          end
          h
        with
          None -> cont None
        | Some ((g, targs_rest, coef, istart', iend', args_rest), h) ->
          if g == array_slice_symb then
            let [elems] = args_rest in
            let split_after elems h =
              let elem = get_unique_var_symb_non_ghost "elem" elem_tp in
              let elems_tail = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
              assume (ctxt#mk_eq elems (mk_cons elem_tp elem elems_tail)) $. fun () ->
              let chunk1 = Chunk ((array_element_symb, true), [elem_tp], coef, [arr; index; elem], None) in
              let chunk2 = Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; ctxt#mk_add index (ctxt#mk_intlit 1); iend'; elems_tail], None) in
              cont (Some (chunk1::chunk2::h))
            in
            if ctxt#query (ctxt#mk_eq istart' index) then
              split_after elems h
            else
              let elems1 = mk_take (ctxt#mk_sub index istart') elems in
              let elems2 = mk_drop (ctxt#mk_sub index istart') elems in
              assume (ctxt#mk_eq elems (mk_append elems1 elems2)) $. fun () ->
              let chunk0 = Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; istart'; index; elems1], None) in
              split_after elems2 (chunk0::h)
          else
            let [ta; tv] = targs_rest in
            let [p; a; elems; vs] = args_rest in
            let n1 = ctxt#mk_sub index istart' in
            let elems1 = mk_take n1 elems in
            let vs1 = mk_take n1 vs in
            let elems2 = mk_drop n1 elems in
            let vs2 = mk_drop n1 vs in
            let elem = get_unique_var_symb "elem" elem_tp in
            let tail_elems2 = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
            let v = get_unique_var_symb "value" tv in
            let tail_vs2 = get_unique_var_symb "values" (InductiveType ("list", [tv])) in
            assume (ctxt#mk_eq elems2 (mk_cons elem_tp elem tail_elems2)) $. fun () ->
            assume (ctxt#mk_eq vs2 (mk_cons tv v tail_vs2)) $. fun () ->
            let before_chunks = 
              if definitely_equal istart' index then
                []
              else
                [Chunk ((array_slice_deep_symb, true), [elem_tp; ta; tv], coef, [arr; istart'; index; p; a; elems1; vs1], None)]
            in
            let after_chunks = 
              if definitely_equal (ctxt#mk_add index (ctxt#mk_intlit 1)) iend' then
                []
              else
                [Chunk ((array_slice_deep_symb, true), [elem_tp; ta; tv], coef, [arr; ctxt#mk_add index (ctxt#mk_intlit 1); iend'; p; a; tail_elems2; tail_vs2], None)]
            in
            let element_chunk = Chunk ((array_element_symb, true), [elem_tp], coef, [arr; index; elem], None) in
            let h = element_chunk :: before_chunks @ after_chunks @ h in
            match try_assq p predinstmap_by_predfamsymb with
              None -> cont (Some (Chunk ((p, false), [], coef, [a; elem; v], None)::h))
            | Some (xs, wbody) ->
              let tpenv = [] in
              let (pn,ilist) = ("", []) in
              let ghostenv = [] in
              let Some env = zip (List.map fst xs) [a; elem; v] in
              produce_asn tpenv h ghostenv env wbody coef None None $. fun h _ _ ->
              cont (Some h)
      in
      let get_slice_rule h [elem_tp] terms_are_well_typed [arr; istart; iend] cont =
        let extract_slice h cond cont' =
          match extract
            begin function
              Chunk ((g', is_symb), [elem_tp'], coef', [arr'; istart'; iend'; elems'], _) when
                g' == array_slice_symb && unify elem_tp elem_tp' &&
                definitely_equal arr' arr && cond coef' istart' (Some iend') ->
              Some (Some (coef', istart', iend', elems'), None)
            | Chunk ((g', is_symb), [elem_tp'], coef', [arr'; index; elem], _) when
                g' == array_element_symb && unify elem_tp elem_tp' && definitely_equal arr' arr && cond coef' index None ->
              Some (None, Some (coef', index, elem))
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((Some slice, None), h) -> cont' (slice, h)
          | Some ((None, Some (coef', index, elem)), h) ->
            (* Close a unit array_slice chunk *)
            cont' ((coef', index, ctxt#mk_add index (ctxt#mk_intlit 1), mk_list elem_tp [elem]), h)
        in
        if definitely_equal istart iend then (* create empty array by default *)
          cont (Some (Chunk ((array_slice_symb, true), [elem_tp], real_unit, [arr; istart; iend; mk_nil()], None)::h))
        else
          extract_slice h
            begin fun coef' istart' iend' ->
              match iend' with
                None -> definitely_equal istart istart'
              | Some iend' -> ctxt#query (ctxt#mk_and (ctxt#mk_le istart' istart) (ctxt#mk_le istart iend'))
            end $.
          fun ((coef, istart0, iend0, elems0), h) ->
          let mk_chunk istart iend elems remove_if_empty =
            if remove_if_empty && (definitely_equal istart iend) then
              []
            else
              [Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; istart; iend; elems], None)]
          in
          let before_length = ctxt#mk_sub istart istart0 in
          let elems0_before = mk_take before_length elems0 in
          let elems0_notbefore = mk_drop before_length elems0 in
          assume (ctxt#mk_eq elems0 (mk_append elems0_before elems0_notbefore)) $. fun () ->
          let chunks_before = mk_chunk istart0 istart elems0_before true in
          let slices = [(istart, iend0, elems0_notbefore)] in
          let rec find_slices slices curr_end h cont' =
            if ctxt#query (ctxt#mk_le iend curr_end) then
              (* found a list of chunks all the way to the end *)
              cont' (slices, h)
            else
              (* need to consume more chunks *)
            extract_slice h (fun coef'' istart'' end'' -> definitely_equal coef coef'' && definitely_equal istart'' curr_end) $.
            fun ((_, istart'', iend'', elems''), h) ->
            find_slices ((istart'', iend'', elems'')::slices) iend'' h cont'
          in
          find_slices slices iend0 h $. fun ((istart_last, iend_last, elems_last)::slices, h) ->
          let length_last = ctxt#mk_sub iend istart_last in
          let elems_last_notafter = mk_take length_last elems_last in
          let elems_last_after = mk_drop length_last elems_last in
          assume (ctxt#mk_eq elems_last (mk_append elems_last_notafter elems_last_after)) $. fun () ->
          let slices = List.rev ((istart_last, iend, elems_last_notafter)::slices) in
          let rec mk_concat lists =
            match lists with
              [] -> mk_nil()
            | [l] -> l
            | l::ls -> mk_append l (mk_concat ls)
          in
          let target_elems = mk_concat (List.map (fun (istart, iend, elems) -> elems) slices) in
          let target_chunk = mk_chunk istart iend target_elems false in
          let chunks_after = mk_chunk iend iend_last elems_last_after true in
          cont (Some (target_chunk @ chunks_before @ chunks_after @ h))
      in
      let get_slice_deep_rule h [elem_tp; a_tp; v_tp] terms_are_well_typed [arr; istart; iend; p; info] cont = 
        let extract_slice_deep h cond cont' =
          match extract
            begin function
              Chunk ((g', is_symb), [elem_tp'; a_tp'; v_tp'], coef', [arr'; istart'; iend'; p'; info'; elems'; vs'], _) when
                g' == array_slice_deep_symb && unify elem_tp elem_tp' && unify a_tp a_tp' && unify v_tp v_tp' &&
                definitely_equal arr' arr && definitely_equal p p' && definitely_equal info info' && cond coef' istart' (Some iend') ->
              Some (Some (coef', istart', iend', elems', vs'), None)
            | Chunk ((g', is_symb), [elem_tp'], coef', [arr'; index; elem], _) when
                g' == array_element_symb && unify elem_tp elem_tp' && definitely_equal arr' arr && cond coef' index None ->
              Some (None, Some (coef', index, elem))
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((Some slice, None), h) -> cont' (slice, h)
          | Some ((None, Some (coef', index, elem)), h) ->
            (* Close a unit array_slice_deep chunk *)
            (* First check if there is a p(info, elem, ?value) chunk *)
            begin fun cont'' ->
              match
                extract
                  begin function
                    Chunk ((g, is_symb), [], coef'', [arg''; elem''; value''], _) when
                      g == p && definitely_equal coef'' coef' && definitely_equal arg'' info && definitely_equal elem'' elem ->
                      Some value''
                  | _ -> None
                  end
                  h
              with
                Some (v, h) -> cont'' v h
              | None ->
                (* Try to close p(info, elem, ?value) *)
                match try_assq p predinstmap_by_predfamsymb with
                  None -> cont None
                | Some (xs, wbody) ->
                  let tpenv = [] in
                  let (pn,ilist) = ("", []) in
                  let ghostenv = [] in
                  let [xinfo, _; xelem, _; xvalue, _] = xs in
                  let env = [xinfo, info; xelem, elem] in
                  let rules = !rules_cell in
                  with_context (Executing (h, env, asn_loc wbody, "Auto-closing array slice")) $. fun () ->
                  consume_asn rules tpenv h ghostenv env wbody true coef' $. fun _ h ghostenv env size_first ->
                  match try_assoc xvalue env with
                    None -> cont None
                  | Some v -> cont'' v h
            end $. fun v h ->
            cont' ((coef', index, ctxt#mk_add index (ctxt#mk_intlit 1), mk_list elem_tp [elem], mk_list v_tp [v]), h)
        in
        if definitely_equal istart iend then (* create empty array by default *)
          cont (Some (Chunk ((array_slice_deep_symb, true), [elem_tp; a_tp; v_tp], real_unit, [arr; istart; iend; p; info; mk_nil(); mk_nil()], None)::h))
        else
          extract_slice_deep h
            begin fun coef' istart' iend' ->
              match iend' with
                None -> definitely_equal istart istart'
              | Some iend' -> ctxt#query (ctxt#mk_and (ctxt#mk_le istart' istart) (ctxt#mk_le istart iend'))
            end $.
          fun ((coef, istart0, iend0, elems0, vs0), h) ->
          let mk_chunk istart iend elems vs =
            Chunk ((array_slice_deep_symb, true), [elem_tp; a_tp; v_tp], coef, [arr; istart; iend; p; info; elems; vs], None)
          in
          let before_length = ctxt#mk_sub istart istart0 in
          let chunk_before = mk_chunk istart0 istart (mk_take before_length elems0) (mk_take before_length vs0) in
          let slices = [(istart, iend0, mk_drop before_length elems0, mk_drop before_length vs0)] in
          let rec find_slices slices curr_end h cont' =
            if ctxt#query (ctxt#mk_le iend curr_end) then
              (* found a list of chunks all the way to the end *)
              cont' (slices, h)
            else
              (* need to consume more chunks *)
            extract_slice_deep h (fun coef'' istart'' end'' -> definitely_equal coef coef'' && definitely_equal istart'' curr_end) $.
            fun ((_, istart'', iend'', elems'', vs''), h) ->
            find_slices ((istart'', iend'', elems'', vs'')::slices) iend'' h cont'
          in
          find_slices slices iend0 h $. fun ((istart_last, iend_last, elems_last, vs_last)::slices, h) ->
          let length_last = ctxt#mk_sub iend istart_last in
          let slices = List.rev ((istart_last, iend, mk_take length_last elems_last, mk_take length_last vs_last)::slices) in
          let rec mk_concat lists =
            match lists with
              [] -> mk_nil()
            | [l] -> l
            | l::ls -> mk_append l (mk_concat ls)
          in
          let target_elems = mk_concat (List.map (fun (istart, iend, elems, vs) -> elems) slices) in
          let target_vs = mk_concat (List.map (fun (istart, iend, elems, vs) -> vs) slices) in
          let target_chunk = mk_chunk istart iend target_elems target_vs in
          let chunk_after = mk_chunk iend iend_last (mk_drop length_last elems_last) (mk_drop length_last vs_last) in
          cont (Some (target_chunk::chunk_before::chunk_after::h))
      in
      begin
      add_rule array_element_symb get_element_rule;
      add_rule array_slice_symb get_slice_rule;
      add_rule array_slice_deep_symb get_slice_deep_rule
      end
    end;
    List.map (fun (predSymb, rules) -> (predSymb, !rules)) !rulemap
  in
  
  rules_cell := rules;

  let rec block_assigned_variables ss =
    match ss with
      [] -> []
    | s::ss -> assigned_variables s @ block_assigned_variables ss
  and expr_assigned_variables e =
    match e with
      Operation (l, op, es, _) -> flatmap expr_assigned_variables es
    | Read (l, e, f) -> expr_assigned_variables e
    | WRead (l, e, fparent, fname, frange, fstatic, fvalue, fghost) -> expr_assigned_variables e
    | ReadArray (l, ea, ei) -> expr_assigned_variables ea @ expr_assigned_variables ei
    | Deref (l, e, _) -> expr_assigned_variables e
    | CallExpr (l, g, _, _, pats, _) -> flatmap (function (LitPat e) -> expr_assigned_variables e | _ -> []) pats
    | ExprCallExpr (l, e, es) -> flatmap expr_assigned_variables (e::es)
    | WPureFunCall (l, g, targs, args) -> flatmap expr_assigned_variables args
    | WPureFunValueCall (l, e, es) -> flatmap expr_assigned_variables (e::es)
    | WMethodCall (l, cn, m, pts, args, mb) -> flatmap expr_assigned_variables args
    | NewArray (l, te, e) -> expr_assigned_variables e
    | NewArrayWithInitializer (l, te, es) -> flatmap expr_assigned_variables es
    | IfExpr (l, e1, e2, e3) -> expr_assigned_variables e1 @ expr_assigned_variables e2 @ expr_assigned_variables e3
    | SwitchExpr (l, e, cs, cdef_opt, _) ->
      expr_assigned_variables e @ flatmap (fun (SwitchExprClause (l, ctor, xs, e)) -> expr_assigned_variables e) cs @ (match cdef_opt with None -> [] | Some (l, e) -> expr_assigned_variables e)
    | CastExpr (l, trunc, te, e) -> expr_assigned_variables e
    | Upcast (e, fromType, toType) -> expr_assigned_variables e
    | WidenedParameterArgument e -> expr_assigned_variables e
    | AddressOf (l, e) -> expr_assigned_variables e
    | AssignExpr (l, Var (_, x, _), e) -> [x] @ expr_assigned_variables e
    | AssignExpr (l, e1, e2) -> expr_assigned_variables e1 @ expr_assigned_variables e2
    | AssignOpExpr (l, Var (_, x, _), op, e, _, _, _) -> [x] @ expr_assigned_variables e
    | AssignOpExpr (l, e1, op, e2, _, _, _) -> expr_assigned_variables e1 @ expr_assigned_variables e2
    | InstanceOfExpr(_, e, _) -> expr_assigned_variables e
    | SuperMethodCall(_, _, args) -> flatmap expr_assigned_variables args
    | WSuperMethodCall(_, _, args, _) -> flatmap expr_assigned_variables args
    | _ -> []
  and assigned_variables s =
    match s with
      PureStmt (l, s) -> assigned_variables s
    | NonpureStmt (l, _, s) -> assigned_variables s
    | ExprStmt e -> expr_assigned_variables e
    | DeclStmt (l, xs) -> flatmap (fun (_, _, x, e, _) -> (match e with None -> [] | Some e -> expr_assigned_variables e)) xs
    | IfStmt (l, e, ss1, ss2) -> expr_assigned_variables e @ block_assigned_variables ss1 @ block_assigned_variables ss2
    | ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause, body) ->
      expr_assigned_variables e @
      begin
        match body with
          None -> []
        | Some s -> assigned_variables s
      end
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) -> []
    | SwitchStmt (l, e, cs) -> expr_assigned_variables e @ flatmap (fun swtch -> match swtch with (SwitchStmtClause (_, _, ss)) -> block_assigned_variables ss | (SwitchStmtDefaultClause(_, ss)) -> block_assigned_variables ss) cs
    | Assert (l, p) -> []
    | Leak (l, p) -> []
    | Open (l, target, g, targs, ps0, ps1, coef) -> []
    | Close (l, target, g, targs, ps0, ps1, coef) -> []
    | ReturnStmt (l, e) -> (match e with None -> [] | Some e -> expr_assigned_variables e)
    | WhileStmt (l, e, p, d, ss) -> expr_assigned_variables e @ block_assigned_variables ss
    | Throw (l, e) -> expr_assigned_variables e
    | TryCatch (l, body, catches) -> block_assigned_variables body @ flatmap (fun (l, t, x, body) -> block_assigned_variables body) catches
    | TryFinally (l, body, lf, finally) -> block_assigned_variables body @ block_assigned_variables finally
    | BlockStmt (l, ds, ss, _, _) -> block_assigned_variables ss
    | PerformActionStmt (lcb, nonpure_ctxt, bcn, pre_boxargs, lch, pre_handlepredname, pre_handlepredargs, lpa, actionname, actionargs, body, closeBraceLoc, post_boxargs, lph, post_handlepredname, post_handlepredargs) ->
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
    | Break _ -> []
    | SuperConstructorCall(_, es) -> flatmap (fun e -> expr_assigned_variables e) es
  in

  let dummypat = SrcPat DummyPat in
  
  let get_points_to h p predSymb l cont =
    consume_chunk rules h [] [] [] l (predSymb, true) [] real_unit dummypat (Some 1) [TermPat p; dummypat] (fun chunk h coef [_; t] size ghostenv env env' ->
      cont h coef t)
  in
    
  let get_field h t fparent fname l cont =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
    get_points_to h t f_symb l cont
  in
  
  let get_full_field (pn,ilist) h t fparent fname l cont =
    let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
    consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit (TermPat real_unit) (Some 1) [TermPat t; dummypat] (fun chunk h coef [_; field_value] size ghostenv env env' ->
      cont h coef field_value)
  in
  
  let current_thread_name = "currentThread" in
  let current_thread_type = IntType in
  
  (** Used to produce malloc'ed, global, local, or nested C variables/objects. *)
  let rec produce_c_object l coef addr tp init allowGhostFields h cont =
    match tp with
      StaticArrayType (elemTp, elemCount) ->
      let (_, _, _, _, c_array_symb, _) = List.assoc "array" predfammap in
      let produce_char_array_chunk h addr elemCount =
        let elems = get_unique_var_symb "elems" (InductiveType ("list", [Char])) in
        let length = ctxt#mk_mul (ctxt#mk_intlit elemCount) (sizeof l elemTp) in
        begin fun cont ->
          if init <> None then
            assume (mk_all_eq Char elems (ctxt#mk_intlit 0)) cont
          else
            cont ()
        end $. fun () ->
        assume_eq (mk_length elems) length $. fun () ->
        cont (Chunk ((c_array_symb, true), [Char], coef, [addr; length; ctxt#mk_intlit 1; char_pred_symb (); elems], None)::h)
      in
      let produce_array_chunk addr elems elemCount =
        match try_pointee_pred_symb elemTp with
          Some elemPred ->
          let length = ctxt#mk_intlit elemCount in
          assume_eq (mk_length elems) length $. fun () ->
          cont (Chunk ((c_array_symb, true), [elemTp], coef, [addr; length; sizeof l elemTp; elemPred; elems], None)::h)
        | None -> (* Produce a character array of the correct size *)
          produce_char_array_chunk h addr elemCount
      in
      begin match elemTp, init with
        Char, Some (Some (StringLit (_, s))) ->
        produce_array_chunk addr (mk_char_list_of_c_string elemCount s) elemCount
      | (StructType _ | StaticArrayType (_, _)), Some (Some (InitializerList (ll, es))) ->
        let size = sizeof l elemTp in
        let rec iter h i es =
          let addr = ctxt#mk_add addr (ctxt#mk_mul (ctxt#mk_intlit i) size) in
          match es with
            [] ->
            produce_char_array_chunk h addr (elemCount - i)
          | e::es ->
            begin fun cont ->
              match elemTp with
                StructType sn ->
                (* Generate struct padding chunk for array elements. *)
                let (_, _, padding_predsymb_opt) = List.assoc sn structmap in
                match padding_predsymb_opt with
                  None -> cont h
                | Some padding_predsymb ->
                  cont (Chunk ((padding_predsymb, true), [], real_unit, [addr], None)::h)
              | _ -> cont h
            end $. fun h ->
            produce_c_object l coef addr elemTp (Some (Some e)) false h $. fun h ->
            iter h (i + 1) es
        in
        iter h 0 es
      | _, Some (Some (InitializerList (ll, es))) ->
        let rec iter n es =
          match es with
            [] -> mk_zero_list n
          | e::es ->
            mk_cons elemTp (eval None [] e) (iter (n - 1) es)
        in
        produce_array_chunk addr (iter elemCount es) elemCount
      | _ ->
        let elems = get_unique_var_symb "elems" (InductiveType ("list", [elemTp])) in
        begin fun cont ->
          match init, elemTp with
            Some _, (IntType|UShortType|ShortType|UintPtrType|UChar|Char|PtrType _) ->
            assume (mk_all_eq elemTp elems (ctxt#mk_intlit 0)) cont
          | _ ->
            cont ()
        end $. fun () ->
        produce_array_chunk addr elems elemCount
      end
    | StructType sn ->
      let fields =
        match List.assoc sn structmap with
          (_, None, _) -> static_error l (Printf.sprintf "Cannot produce an object of type 'struct %s' since this struct was declared without a body" sn) None
        | (_, Some fds, _) -> fds
      in
      let inits =
        match init with
          Some (Some (InitializerList (_, es))) -> Some (Some es)
        | Some None -> Some None (* Initialize to default value (= zero) *)
        | _ -> None (* Do not initialize; i.e. arbitrary initial value *)
      in
      let rec iter h fields inits =
        match fields with
          [] -> cont h
        | (f, (lf, gh, t))::fields ->
          if gh = Ghost && not allowGhostFields then static_error l "Cannot produce a struct instance with ghost fields in this context." None;
          let init, inits =
            if gh = Ghost then None, inits else
            match inits with
              Some (Some (e::es)) -> Some (Some e), Some (Some es)
            | Some (None | Some []) -> Some None, Some None
            | _ -> None, None
          in
          match t with
            StaticArrayType (_, _) | StructType _ ->
            produce_c_object l coef (field_address l addr sn f) t init allowGhostFields h $. fun h ->
            iter h fields inits
          | _ ->
            let value =
              match init with
                Some None ->
                begin match provertype_of_type t with
                  ProverBool -> ctxt#mk_false
                | ProverInt -> ctxt#mk_intlit 0
                | ProverReal -> real_zero
                | ProverInductive -> get_unique_var_symb_ "value" t (gh = Ghost)
                end
              | Some (Some e) -> eval None [] e
              | None -> get_unique_var_symb_ "value" t (gh = Ghost)
            in
            assume_field h sn f t gh addr value coef $. fun h ->
            iter h fields inits
      in
      iter h fields inits
    | _ ->
      let value =
        match init with
          Some None -> ctxt#mk_intlit 0
        | Some (Some e) -> eval None [] e
        | None -> get_unique_var_symb "value" tp
      in
      cont (Chunk ((pointee_pred_symb l tp, true), [], coef, [addr; value], None)::h)
  in
  
  let rec consume_c_object l addr tp h cont =
    match tp with
      StaticArrayType (elemTp, elemCount) ->
      let (_, _, _, _, c_array_symb, _) = List.assoc "array" predfammap in
      begin match try_pointee_pred_symb elemTp with
        Some elemPred ->
        let pats = [TermPat addr; TermPat (ctxt#mk_intlit elemCount); TermPat (sizeof l elemTp); TermPat elemPred; dummypat] in
        consume_chunk rules h [] [] [] l (c_array_symb, true) [elemTp] real_unit real_unit_pat (Some 4) pats $. fun _ h _ _ _ _ _ _ ->
        cont h
      | None ->
        let pats = [TermPat addr; TermPat (sizeof l tp); TermPat (ctxt#mk_intlit 1); TermPat (char_pred_symb ()); dummypat] in
        consume_chunk rules h [] [] [] l (c_array_symb, true) [Char] real_unit real_unit_pat (Some 4) pats $. fun _ h _ _ _ _ _ _ ->
        cont h
      end
    | StructType sn ->
      let fields =
        match List.assoc sn structmap with
          (_, None, _) -> static_error l (Printf.sprintf "Cannot consume an object of type 'struct %s' since this struct was declared without a body" sn) None
        | (_, Some fds, _) -> fds
      in
      let rec iter h fields =
        match fields with
          [] -> cont h
        | (f, (lf, gh, t))::fields ->
          match t with
            StaticArrayType (_, _) | StructType _ ->
            consume_c_object l (field_address l addr sn f) t h $. fun h ->
            iter h fields
          | _ ->
            get_field h addr sn f l $. fun h coef _ ->
            if not (definitely_equal coef real_unit) then assert_false h [] l "Full field chunk permission required" None;
            iter h fields
      in
      iter h fields
    | _ ->
      consume_chunk rules h [] [] [] l (pointee_pred_symb l tp, true) [] real_unit real_unit_pat (Some 1) [TermPat addr; dummypat] $. fun _ h _ _ _ _ _ _ ->
      cont h
  in
  
  (* Region: function contracts *)
  
  let functypemap1 =
    let rec iter functypemap ds =
      match ds with
        [] -> List.rev functypemap
      | (ftn, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, predfammaps))::ds ->
        let (pre, post) =
          let (wpre, tenv) = check_asn (pn,ilist) tparams (ftxmap @ xmap @ [("this", PtrType Void); (current_thread_name, current_thread_type)]) pre in
          let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
          let (wpost, tenv) = check_asn (pn,ilist) tparams postmap post in
          (wpre, wpost)
        in
        iter ((ftn, (l, gh, tparams, rt, ftxmap, xmap, pre, post, predfammaps))::functypemap) ds
    in
    iter [] functypedeclmap1
  in
  
  let functypemap = functypemap1 @ functypemap0 in
  
  let check_breakpoint h env ((((basepath, relpath), line, col), _) as l) =
    match breakpoint with
      None -> ()
    | Some (path0, line0) ->
      if line = line0 && Filename.concat basepath relpath = path0 then
        assert_false h env l "Breakpoint reached." None
  in

  let is_empty_chunk name targs frac args =
    List.exists
    (fun (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) ->
      predname_eq (symb, true) name &&
      let indexCount = List.length fns in
      let Some n = inputParamCount in
      let (inputParams, outputParams) = take_drop n xs in
      let Some tpenv = zip predinst_tparams targs in
      let (indices, real_args) = take_drop indexCount args in
      let (inputArgs, outputArgs) = take_drop n real_args in
      List.for_all2 definitely_equal indices fsymbs &&
      let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
      List.exists (fun conds -> List.for_all (fun cond -> ctxt#query (eval None env cond)) conds) conds
    )
    empty_preds
  in
  
  let check_leaks h env l msg = (* ?check_leaks *)
    match file_type path with
    Java -> with_context (Executing (h, env, l, "Leaking remaining chunks")) $. fun () -> check_breakpoint h env l
    | _ ->
    with_context (Executing (h, env, l, "Cleaning up dummy fraction chunks")) $. fun () ->
    let h = List.filter (fun (Chunk (_, _, coef, _, _)) -> not (is_dummy_frac_term coef)) h in
    with_context (Executing (h, env, l, "Leak check.")) $. fun () ->
    let h = List.filter (function (Chunk(name, targs, frac, args, _)) when is_empty_chunk name targs frac args -> false | _ -> true) h in
    let check_plugin_state h env l symb state =
      let [_, ((_, plugin), _)] = pluginmap in
      match plugin#check_leaks state with
        None -> ()
      | Some msg -> assert_false h env l msg None
    in
    let h = List.filter (function Chunk ((name, true), targs, frac, args, Some (PluginChunkInfo info)) -> check_plugin_state h env l name info; false | _ -> true) h in
    if h <> [] then assert_false h env l msg (Some "leak");
    check_breakpoint [] env l
  in
  
  let check_func_header_compat l msg env00 (k, tparams, rt, xmap, nonghost_callers_only, pre, post, epost) (k0, tparams0, rt0, xmap0, nonghost_callers_only0, tpenv0, cenv0, pre0, post0, epost0) =
    if k <> k0 then 
      if (not (is_lemma k)) || (not (is_lemma k0)) then
        static_error l (msg ^ "Not the same kind of function.") None;
    let tpenv =
      match zip tparams tparams0 with
        None -> static_error l (msg ^ "Type parameter counts do not match.") None
      | Some bs -> List.map (fun (x, x0) -> (x, TypeParam x0)) bs
    in
    begin
      match (rt, rt0) with
        (None, None) -> ()
      | (Some rt, Some rt0) -> expect_type_core l (msg ^ "Return types: ") (instantiate_type tpenv rt) rt0
      | _ -> static_error l (msg ^ "Return types do not match.") None
    end;
    begin
      (if (List.length xmap) > (List.length xmap0) then static_error l (msg ^ "Implementation has more parameters than prototype.") None);
      List.iter 
        (fun ((x, t), (x0, t0)) ->
           expect_type_core l (msg ^ "Parameter '" ^ x ^ "': ") t0 (instantiate_type tpenv t);
        )
        (zip2 xmap xmap0)
    end;
    if nonghost_callers_only <> nonghost_callers_only0 then static_error l (msg ^ "nonghost_callers_only clauses do not match.") None;
    push();
    let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
    let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
    let env0 = currentThreadEnv @ env0_0 @ cenv0 in
    produce_asn tpenv0 [] [] env0 pre0 real_unit None None (fun h _ env0 ->
      let bs = zip2 xmap env0_0 in
      let env = currentThreadEnv @ List.map (fun ((p, _), (p0, v)) -> (p, v)) bs @ env00 in
      consume_asn rules tpenv h [] env pre true real_unit (fun _ h _ env _ ->
        let (env, env0) =
          match rt with
            None -> (env, env0)
          | Some t -> let result = get_unique_var_symb "result" t in (("result", result)::env, ("result", result)::env0)
        in
        produce_asn tpenv h [] env post real_unit None None (fun h _ _ ->
          consume_asn rules tpenv0 h [] env0 post0 true real_unit (fun _ h _ env0 _ ->
            check_leaks h env0 l (msg ^ "Implementation leaks heap chunks.")
          )
        );
        List.iter (fun (exceptp, epost) ->
          if not (is_unchecked_exception_type exceptp) then
            produce_asn tpenv h [] env epost real_unit None None (fun h _ _ ->
              let rec handle_exception handlers =
                match handlers with
                | [] -> assert_false h env l ("Potentially unhandled exception " ^ (string_of_type exceptp) ^ ".") None 
                | (handler_tp, epost0) :: handlers ->
                  branch
                   (fun () ->
                      if (is_subtype_of_ exceptp handler_tp) || (is_subtype_of_ handler_tp exceptp) then
                      consume_asn rules tpenv0 h [] env0 epost0 true real_unit (fun _ h ghostenv env size_first -> ())
                   )
                   (fun () ->
                     if not (is_subtype_of_ exceptp handler_tp) then
                       handle_exception handlers
                   )
              in
              handle_exception epost0
            )
        ) epost;
      )
    );
    pop()
  in
  
  let assume_is_functype fn ftn =
    let (_, _, _, _, symb) = List.assoc ("is_" ^ ftn) purefuncmap in
    ignore (ctxt#assume (ctxt#mk_eq (mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true))
  in
  
  let functypes_implemented = ref [] in
  
  let check_func_header pn ilist tparams0 tenv0 env0 l k tparams rt fn fterm xs nonghost_callers_only functype_opt contract_opt body =
    if tparams0 <> [] then static_error l "Declaring local functions in the scope of type parameters is not yet supported." None;
    check_tparams l tparams0 tparams;
    let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) tparams rt) in
    let xmap =
      let rec iter xm xs =
        match xs with
          [] -> List.rev xm
        | (te, x)::xs ->
          if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
          if List.mem_assoc x tenv0 then static_error l ("Parameter '" ^ x ^ "' hides existing variable '" ^ x ^ "'.") None;
          let t = check_pure_type (pn,ilist) tparams te in
          iter ((x, t)::xm) xs
      in
      iter [] xs
    in
    let tenv = [(current_thread_name, current_thread_type)] @ xmap @ tenv0 in
    let (pre, pre_tenv, post) =
      match contract_opt with
        None -> static_error l "Non-fixpoint function must have contract." None
      | Some (pre, post) ->
        let (wpre, pre_tenv) = check_asn (pn,ilist) tparams tenv pre in
        let postmap = match rt with None -> pre_tenv | Some rt -> ("result", rt)::pre_tenv in
        let (wpost, tenv) = check_asn (pn,ilist) tparams postmap post in
        (wpre, pre_tenv, wpost)
    in
    if nonghost_callers_only then begin
      match k with
        Regular -> static_error l "Only lemma functions can be marked nonghost_callers_only." None
      | Lemma(true, _) -> static_error l "Lemma functions marked nonghost_callers_only cannot be autolemmas." None
      | Lemma(false, _) -> ()
    end;
    let functype_opt =
      match functype_opt with
        None -> None
      | Some (ftn, fttargs, ftargs) ->
        if body = None then static_error l "A function prototype cannot implement a function type." None;
        begin
          match resolve (pn,ilist) l ftn functypemap with
            None -> static_error l "No such function type." None
          | Some (ftn, (lft, gh, fttparams, rt0, ftxmap0, xmap0, pre0, post0, ft_predfammaps)) ->
            let fttargs = List.map (check_pure_type (pn,ilist) []) fttargs in
            let fttpenv =
              match zip fttparams fttargs with
                None -> static_error l "Incorrect number of function type type arguments" None
              | Some bs -> bs
            in
            let ftargenv =
              match zip ftxmap0 ftargs with
                None -> static_error l "Incorrect number of function type arguments" None
              | Some bs ->
                List.map
                  begin fun ((x, tp), (larg, arg)) ->
                    let value =
                      match try_assoc arg modulemap with
                        None -> static_error larg "No such module" None
                      | Some term -> term
                    in
                    expect_type larg IntType (instantiate_type fttpenv tp);
                    (x, value)
                  end
                  bs
            in
            let Some fterm = fterm in
            let cenv0 = [("this", fterm)] @ ftargenv in
            let k' = match gh with Real -> Regular | Ghost -> Lemma(true, None) in
            let xmap0 = List.map (fun (x, t) -> (x, instantiate_type fttpenv t)) xmap0 in
            check_func_header_compat l "Function type implementation check: " env0
              (k, tparams, rt, xmap, nonghost_callers_only, pre, post, [])
              (k', [], rt0, xmap0, false, fttpenv, cenv0, pre0, post0, []);
            if gh = Real then
            begin
              if ftargs = [] then
                assume_is_functype fn ftn;
              if not (List.mem_assoc ftn functypemap1) then
                functypes_implemented := (fn, lft, ftn, List.map snd ftargs, unloadable)::!functypes_implemented
            end;
            Some (ftn, ft_predfammaps, fttargs, ftargs)
        end
    in
    (rt, xmap, functype_opt, pre, pre_tenv, post)
  in
  
  let (funcmap1, prototypes_implemented) =
    let rec iter pn ilist funcmap prototypes_implemented ds =
      match ds with
        [] -> (funcmap, List.rev prototypes_implemented)
      | Func (l, k, tparams, rt, fn, xs, nonghost_callers_only, functype_opt, contract_opt, body,Static,Public)::ds when k <> Fixpoint ->
        let fn = full_name pn fn in
        let fterm = Some (List.assoc fn funcnameterms) in
        let (rt, xmap, functype_opt, pre, pre_tenv, post) =
          check_func_header pn ilist [] [] [] l k tparams rt fn fterm xs nonghost_callers_only functype_opt contract_opt body
        in
        begin
          let body' = match body with None -> None | Some body -> Some (Some body) in
          match try_assoc2 fn funcmap funcmap0 with
            None -> iter pn ilist ((fn, FuncInfo ([], fterm, l, k, tparams, rt, xmap, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body',Static,Public))::funcmap) prototypes_implemented ds
          | Some (FuncInfo ([], fterm0, l0, k0, tparams0, rt0, xmap0, nonghost_callers_only0, pre0, pre_tenv0, post0, _, Some _,Static,Public)) ->
            if body = None then
              static_error l "Function prototype must precede function implementation." None
            else
              static_error l "Duplicate function implementation." None
          | Some (FuncInfo ([], fterm0, l0, k0, tparams0, rt0, xmap0, nonghost_callers_only0, pre0, pre_tenv0, post0, functype_opt0, None,Static,Public)) ->
            if body = None then static_error l "Duplicate function prototype." None;
            check_func_header_compat l "Function prototype implementation check: " [] (k, tparams, rt, xmap, nonghost_callers_only, pre, post, []) (k0, tparams0, rt0, xmap0, nonghost_callers_only0, [], [], pre0, post0, []);
            iter pn ilist ((fn, FuncInfo ([], fterm, l, k, tparams, rt, xmap, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body',Static,Public))::funcmap) ((fn, l0)::prototypes_implemented) ds
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
  
  let interfmap1 =
    List.map
      begin fun (ifn, (l, fieldmap, specs, preds, interfs, pn, ilist)) ->
        let mmap =
        let rec iter mmap meth_specs =
          match meth_specs with
            [] -> List.rev mmap
          | Meth (lm, gh, rt, n, ps, co, body, binding, _, _)::meths ->
            if body <> None then static_error lm "Interface method cannot have body" None;
            if binding = Static then static_error lm "Interface method cannot be static" None;
            let xmap =
              let rec iter xm xs =
                match xs with
                 [] -> List.rev xm
               | (te, x)::xs ->
                 if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
                 let t = check_pure_type (pn,ilist) [] te in
                 iter ((x, t)::xm) xs
              in
              iter [] ps
            in
            let sign = (n, List.map snd (List.tl xmap)) in
            if List.mem_assoc sign mmap then static_error lm "Duplicate method" None;
            let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
            let (pre, pre_tenv, post, epost) =
              match co with
                None -> static_error lm ("Non-fixpoint function must have contract: "^n) None
              | Some (pre, post, epost) ->
                let (pre, tenv) = check_asn (pn,ilist) [] ((current_thread_name, current_thread_type)::xmap) pre in
                let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
                let (post, _) = check_asn (pn,ilist) [] postmap post in
                let epost = List.map (fun (tp, epost) -> 
                  let (epost, _) = check_asn (pn,ilist) [] tenv epost in
                  let tp = check_pure_type (pn,ilist) [] tp in
                  (tp, epost)
                ) epost in
                (pre, tenv, post, epost)
            in
            iter ((sign, (lm, gh, rt, xmap, pre, pre_tenv, post, epost, Public, true))::mmap) meths
        in
        iter [] specs
        in
        (ifn, InterfaceInfo (l, fieldmap, mmap, preds, interfs))
      end
      interfmap1
  in
  
  let string_of_sign (mn, ts) =
    Printf.sprintf "%s(%s)" mn (String.concat ", " (List.map string_of_type ts))
  in
  
  let () = (* Check interfaces in .java files against their specifications in .javaspec files. *)
    interfmap1 |> List.iter begin function (i, InterfaceInfo (l1,fields1,meths1,preds1,interfs1)) ->
      match try_assoc i interfmap0 with
      | None -> ()
      | Some (InterfaceInfo (l0,fields0,meths0,preds0,interfs0)) ->
        let rec match_fields fields0 fields1 =
          match fields0 with
            [] -> if fields1 <> [] then static_error l1 ".java file does not correct implement .javaspec file: interface declares more fields" None
          | (fn, f0)::fields0 ->
            match try_assoc fn fields1 with
              None -> static_error l1 (".java file does not correctly implement .javaspec file: interface does not declare field " ^ fn) None
            | Some f1 ->
              if f1.ft <> f0.ft then static_error f1.fl ".java file does not correctly implement .javaspec file: field type does not match" None;
              if !(f1.fvalue) <> !(f0.fvalue) then static_error f1.fl ".java file does not correctly implement .javaspec file: field value does not match" None;
              match_fields fields0 (List.remove_assoc fn fields1)
        in
        let rec match_meths meths0 meths1=
          match meths0 with
            [] -> if meths1 <> [] then static_error l1 ".java file does not correctly implement .javaspec file: interface declares more methods" None
          | (sign, (lm0,gh0,rt0,xmap0,pre0,pre_tenv0,post0,epost0,v0,abstract0))::meths0 ->
            match try_assoc sign meths1 with
              None-> static_error l1 (".java file does not correctly implement .javaspec file: interface does not declare method " ^ string_of_sign sign) None
            | Some(lm1,gh1,rt1,xmap1,pre1,pre_tenv1,post1,epost1,v1,abstract1) ->
              check_func_header_compat lm1 "Method specification check: " [] (func_kind_of_ghostness gh1,[],rt1, xmap1,false, pre1, post1, epost1) (func_kind_of_ghostness gh0, [], rt0, xmap0, false, [], [], pre0, post0, epost0);
              match_meths meths0 (List.remove_assoc sign meths1)
        in
        match_fields fields0 fields1;
        match_meths meths0 meths1
    end
  in
  
  let interfmap = (* checks overriding methods in interfaces *)
    let rec iter map0 map1 =
      let interf_specs_for_sign sign itf =
                    let InterfaceInfo (_, fields, meths, _,  _) = List.assoc itf map1 in
                    match try_assoc sign meths with
                      None -> []
                    | Some spec -> [(itf, spec)]
      in
      match map0 with
        [] -> map1
      | (i, InterfaceInfo (l,fields,meths,preds,interfs)) as elem::rest ->
        List.iter (fun (sign, (lm,gh,rt,xmap,pre,pre_tenv,post,epost,v,abstract)) ->
          let superspecs = List.flatten (List.map (fun i -> (interf_specs_for_sign sign i)) interfs) in
          List.iter (fun (tn, (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', vis', abstract')) ->
            if rt <> rt' then static_error lm "Return type does not match overridden method" None;
            if gh <> gh' then
                  begin match gh with
                    Ghost -> static_error lm "A lemma method cannot implement or override a non-lemma method." None
                  | Real -> static_error lm "A non-lemma method cannot implement or override a lemma method." None
            end;
            begin
            push();
            let ("this", thisType)::xmap = xmap in
            let ("this", _)::xmap' = xmap' in
            let thisTerm = get_unique_var_symb "this" thisType in
            check_func_header_compat l "Method specification check: " [("this", thisTerm)]
              (Regular, [], rt, xmap, false, pre, post, epost)
              (Regular, [], rt', xmap', false, [], [("this", thisTerm)], pre', post', epost');
            pop();
            end
          ) superspecs;
        ) meths;
        iter rest (elem :: map1)
    in
    iter interfmap1 interfmap0
  in
  
  let rec dynamic_of asn =
    match asn with
      WInstPredAsn (l, None, st, cfin, tn, g, index, pats) ->
      WInstPredAsn (l, None, st, cfin, tn, g, get_class_of_this, pats)
    | Sep (l, a1, a2) ->
      let a1' = dynamic_of a1 in
      let a2' = dynamic_of a2 in
      if a1' == a1 && a2' == a2 then asn else Sep (l, a1', a2')
    | IfAsn (l, e, a1, a2) ->
      let a1' = dynamic_of a1 in
      let a2' = dynamic_of a2 in
      if a1' == a1 && a2' == a2 then asn else IfAsn (l, e, a1', a2')
    | WSwitchAsn (l, e, i, cs) ->
      let rec iter cs =
        match cs with
          [] -> cs
        | SwitchAsnClause (l, ctor, pats, info, body) as c::cs0 ->
          let body' = dynamic_of body in
          let c' = if body' == body then c else SwitchAsnClause (l, ctor, pats, info, body') in
          let cs0' = iter cs0 in
          if c' == c && cs0' == cs0 then cs else c'::cs0'
      in
      let cs' = iter cs in
      if cs' == cs then asn else WSwitchAsn (l, e, i, cs')
    | CoefAsn (l, coefpat, body) ->
      let body' = dynamic_of body in
      if body' == body then asn else CoefAsn (l, coefpat, body')
    | _ -> asn
  in
  
  let classmap1 =
    let rec iter classmap1_done classmap1_todo =
      let interf_specs_for_sign sign itf =
        let InterfaceInfo (_, _, meths, _,  _) = List.assoc itf interfmap in
        match try_assoc sign meths with
          None -> []
        | Some spec -> [(itf, spec)]
      in
      let rec super_specs_for_sign sign cn itfs =
        class_specs_for_sign sign cn @ flatmap (interf_specs_for_sign sign) itfs
      and class_specs_for_sign sign cn =
        if cn = "" then [] else
        let (super, interfs, mmap) =
          match try_assoc cn classmap1_done with
            Some (l, abstract, fin, mmap, fds, constr, super, interfs, preds, pn, ilist) -> (super, interfs, mmap)
          | None ->
            match try_assoc cn classmap0 with
              Some {csuper; cinterfs; cmeths} -> (csuper, cinterfs, cmeths)
            | None -> assert false
        in
        let specs =
          match try_assoc sign mmap with
          | Some (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, Instance, v, _, abstract) -> [(cn, (lm, gh, rt, xmap, pre_dyn, pre_tenv, post_dyn, epost_dyn, v, abstract))]
          | _ -> []
        in
        specs @ super_specs_for_sign sign super interfs
      in
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist))::classmap1_todo ->
        let cont cl = iter (cl::classmap1_done) classmap1_todo in
        let rec iter mmap meths =
          match meths with
            [] -> cont (cn, (l, abstract, fin, List.rev mmap, fds, constr, super, interfs, preds, pn, ilist))
          | Meth (lm, gh, rt, n, ps, co, ss, fb, v,abstract)::meths ->
            let xmap =
                let rec iter xm xs =
                  match xs with
                   [] -> List.rev xm
                 | (te, x)::xs -> if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
                     let t = check_pure_type (pn,ilist) [] te in
                     iter ((x, t)::xm) xs
                in
                iter [] ps
            in
            let xmap1 = match fb with Static -> xmap | Instance -> let _::xmap1 = xmap in xmap1 in
            let sign = (n, List.map snd xmap1) in
            if List.mem_assoc sign mmap then static_error lm "Duplicate method." None;
            let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
            let co =
              match co with
                None -> None
              | Some (pre, post, epost) ->
                let (wpre, tenv) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::(current_thread_name, current_thread_type)::xmap) pre in
                let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
                let (wpost, _) = check_asn (pn,ilist) [] postmap post in
                let wepost = List.map (fun (tp, epost) -> 
                  let (wepost, _) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::(current_thread_name, current_thread_type)::xmap) epost in
                  let tp = check_pure_type (pn,ilist) [] tp in
                  (tp, wepost)
                ) epost in
                let (wpre_dyn, wpost_dyn, wepost_dyn) = if fb = Static then (wpre, wpost, wepost) else (dynamic_of wpre, dynamic_of wpost, List.map (fun (tp, wepost) -> (tp, dynamic_of wepost)) wepost) in
                Some (wpre, tenv, wpost, wepost, wpre_dyn, wpost_dyn, wepost_dyn)
            in
            let super_specs = if fb = Static then [] else super_specs_for_sign sign super interfs in
            if not is_jarspec then
            List.iter
              begin fun (tn, (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', vis', abstract')) ->
                if gh <> gh' then
                  begin match gh with
                    Ghost -> static_error lm "A lemma method cannot implement or override a non-lemma method." None
                  | Real -> static_error lm "A non-lemma method cannot implement or override a lemma method." None
                  end;
                if rt <> rt' then static_error lm "Return type does not match overridden method" None;
                match co with
                  None -> ()
                | Some (pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn) ->
                  push();
                  let ("this", thisType)::xmap = xmap in
                  let ("this", _)::xmap' = xmap' in
                  let thisTerm = get_unique_var_symb "this" thisType in
                  assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) (fun _ ->
                    check_func_header_compat l "Method specification check: " [("this", thisTerm)]
                      (Regular, [], rt, xmap, false, pre, post, epost)
                      (Regular, [], rt', xmap', false, [], [("this", thisTerm)], pre', post', epost')
                  );
                  pop()
              end
              super_specs;
            let (pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn) =
              match co with
                Some spec -> spec
              | None ->
                match super_specs with
                  (tn, (_, _, _, xmap', pre', pre_tenv', post', epost', _, _))::_ ->
                  if not (List.for_all2 (fun (x, t) (x', t') -> x = x') xmap xmap') then static_error lm (Printf.sprintf "Parameter names do not match overridden method in %s" tn) None;
                  (pre', pre_tenv', post', epost', pre', post', epost')
                | [] -> static_error lm "Method must have contract" None
            in
            let ss = match ss with None -> None | Some ss -> Some (Some ss) in
            iter ((sign, (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, super_specs <> [], abstract))::mmap) meths
        in
        iter [] meths
    in
    iter [] classmap1
  in
  
  let classmap1 =
    List.map
      begin fun (cn, (l, abstract, fin, meths, fds, ctors, super, interfs, preds, pn, ilist)) ->
        let rec iter cmap ctors =
          match ctors with
            [] -> (cn, {cl=l; cabstract=abstract; cfinal=fin; cmeths=meths; cfds=fds; cctors=List.rev cmap; csuper=super; cinterfs=interfs; cpreds=preds; cpn=pn; cilist=ilist})
            | Cons (lm, ps, co, ss, v)::ctors ->
              let xmap =
                let rec iter xm xs =
                  match xs with
                   [] -> List.rev xm
                 | (te, x)::xs ->
                   if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
                   let t = check_pure_type (pn,ilist) [] te in
                   iter ((x, t)::xm) xs
                in
                iter [] ps
              in
              let sign = List.map snd xmap in
              if List.mem_assoc sign cmap then static_error lm "Duplicate constructor" None;
              let (pre, pre_tenv, post, epost) =
                match co with
                  None -> static_error lm "Constructor must have contract" None
                | Some (pre, post, epost) ->
                  let (wpre, tenv) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::xmap) pre in
                  let postmap = ("this", ObjType(cn))::tenv in
                  let (wpost, _) = check_asn (pn,ilist) [] postmap post in
                  let wepost = List.map (fun (tp, epost) -> 
                    let (wepost, _) = check_asn (pn,ilist) [] tenv epost in
                    let tp = check_pure_type (pn,ilist) [] tp in
                    (tp, wepost)
                  ) epost in
                  (wpre, tenv, wpost, wepost)
              in
              let ss' = match ss with None -> None | Some ss -> Some (Some ss) in
               let epost: (type_ * asn) list = epost in
              iter ((sign, (lm, xmap, pre, pre_tenv, post, epost, ss', v))::cmap) ctors
        in
        iter [] ctors
      end
      classmap1
  in
  
  (* Default constructor insertion *)

  let classmap1 =
    if is_jarspec then classmap1 else
    let rec iter classmap1_done classmap1_todo =
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, ({cl=l; cfds=fds; cctors=cmap; csuper=super} as cls)) as c::classmap1_todo ->
        let c =
          if cmap <> [] then c else
          (* Check if superclass has zero-arg ctor *)
          begin fun cont ->
            let {cctors=cmap'} = assoc2 super classmap1_done classmap0 in
            match try_assoc [] cmap' with
              Some (l'', xmap, pre, pre_tenv, post, epost, _, _) ->
              let epost: (type_ * asn) list = epost in
              cont pre pre_tenv post epost
            | None -> c
          end $. fun super_pre super_pre_tenv super_post super_epost ->
          let _::super_pre_tenv = super_pre_tenv in (* Chop off the current_class entry *)
          let post =
            List.fold_left
              begin fun post (f, {fl; ft; fbinding}) ->
                if fbinding = Static then
                  post
                else
                  let default_value =
                    match ft with
                      Bool -> False fl
                    | IntType | ShortType | Char -> IntLit (fl, zero_big_int, ref (Some ft))
                    | ObjType _ | ArrayType _ -> Null fl
                  in
                  Sep (l, post, WPointsTo (fl, WRead (fl, Var (fl, "this", ref (Some LocalVar)), cn, f, ft, false, ref (Some None), Real), ft, LitPat default_value))
              end
              super_post
              fds
          in
          let default_ctor =
            let sign = [] in
            let xmap = [] in
            let ss = Some (Some ([], l)) in
            let vis = Public in
            (sign, (l, xmap, super_pre, (current_class, ClassOrInterfaceName cn)::super_pre_tenv, post, [], ss, vis))
          in
          (cn, {cls with cctors=[default_ctor]})
        in
        iter (c::classmap1_done) classmap1_todo
    in
    iter [] classmap1
  in
  
  (* Merge classmap1 into classmap0; check class implementations against specifications. *)
  let classmap =
    let rec iter map0 map1 =
      match map0 with
        [] -> map1
      | (cn, cls0) as elem::rest ->
        match try_assoc cn map1 with
          None -> iter rest (elem::map1)
        | Some cls1 ->
          if cls1.cfinal <> cls0.cfinal then static_error cls1.cl "Class finality does not match specification." None;
          let match_fds fds0 fds1=
            let rec iter fds0 fds1=
            match fds0 with
              [] -> fds1
            | (f0, {ft=t0; fvis=vis0; fbinding=binding0; ffinal=final0; finit=init0; fvalue=value0}) as elem::rest ->
              match try_assoc f0 fds1 with
                None-> iter rest (elem::fds1)
              | Some {fl=lf1; ft=t1; fvis=vis1; fbinding=binding1; ffinal=final1; finit=init1; fvalue=value1} ->
                let v1 = ! value0 in
                let v2 = ! value1 in
                if t0<>t1 || vis0<>vis1 || binding0<>binding1 || final0<>final1 (*|| v1 <> v2*) then static_error lf1 "Duplicate field" None;
                if !value0 = None && init0 <> None then static_error lf1 "Cannot refine a non-constant field with an initializer." None;
                iter rest fds1
            in
            iter fds0 fds1
          in
          let match_meths meths0 meths1=
            let rec iter meths0 meths1=
              match meths0 with
                [] -> meths1
              | (sign0, (lm0,gh0,rt0,xmap0,pre0,pre_tenv0,post0,epost0,pre_dyn0,post_dyn0,epost_dyn0,ss0,fb0,v0,_,abstract0)) as elem::rest ->
                let epost0: (type_ * asn) list = epost0 in
                match try_assoc sign0 meths1 with
                  None-> iter rest (elem::meths1)
                | Some(lm1,gh1,rt1,xmap1,pre1,pre_tenv1,post1,epost1,pre_dyn1,post_dyn1,epost_dyn1,ss1,fb1,v1,_,abstract1) -> 
                  let epost1: (type_ * asn) list = epost1 in
                  check_func_header_compat lm1 "Method implementation check: " []
                    (func_kind_of_ghostness gh1,[],rt1, xmap1,false, pre1, post1, epost1)
                    (func_kind_of_ghostness gh0, [], rt0, xmap0, false, [], [], pre0, post0, epost0);
                  if ss0=None then meths_impl:=(fst sign0,lm0)::!meths_impl;
                  iter rest meths1
            in
            iter meths0 meths1
          in
          let match_constr constr0 constr1=
            let rec iter constr0 constr1=
              match constr0 with
                [] -> constr1
              | (sign0, (lm0,xmap0,pre0,pre_tenv0,post0,epost0,ss0,v0)) as elem::rest ->
                let epost0: (type_ * asn) list = epost0 in
                match try_assoc sign0 constr1 with
                  None-> iter rest (elem::constr1)
                | Some(lm1,xmap1,pre1,pre_tenv1,post1,epost1,ss1,v1) ->
                  let epost1: (type_ * asn) list = epost1 in
                  let rt= None in
                  check_func_header_compat lm1 "Constructor implementation check: " []
                    (Regular,[],rt, ("this", ObjType cn)::xmap1,false, pre1, post1, epost1)
                    (Regular, [], rt, ("this", ObjType cn)::xmap0, false, [], [], pre0, post0, epost0);
                  if ss0=None then cons_impl:=(cn,lm0)::!cons_impl;
                  iter rest constr1
            in
            iter constr0 constr1
          in
          if cls0.csuper <> cls1.csuper || cls0.cinterfs <> cls1.cinterfs then static_error cls1.cl "Duplicate class" None
          else 
          let meths'= match_meths cls0.cmeths cls1.cmeths in
          let fds'= match_fds cls0.cfds cls1.cfds in
          let constr'= match_constr cls0.cctors cls1.cctors in
          iter rest ((cn, {cls1 with cmeths=meths'; cfds=fds'; cctors=constr'})::map1)
    in
    iter classmap0 classmap1
  in
  
  (* Region: Type checking of field initializers for instance fields *)

  let classmap =
    List.map
      begin fun (cn, ({cfds=fds; cpn=pn; cilist=ilist} as cls)) ->
        let fds =
          List.map
            begin function
              (f, ({ft; fbinding=Instance; finit=Some e} as fd)) ->
              let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e tp in
              let tenv = [(current_class, ClassOrInterfaceName cn); ("this", ObjType cn); (current_thread_name, current_thread_type)] in
              let w = check_expr_t (pn,ilist) [] tenv e ft in
              (f, {fd with finit=Some w})
            | fd -> fd
            end
            fds
        in
        (cn, {cls with cfds=fds})
      end
      classmap
  in
  
  begin
    (* Inheritance check *)
    let rec get_overrides cn =
      if cn = "java.lang.Object" then [] else
      let {cmeths; csuper} = List.assoc cn classmap in
      let overrides =
        flatmap
          begin fun (sign, (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract)) ->
            if is_override || pre != pre_dyn || post != post_dyn then [(cn, sign)] else []
          end
          cmeths
      in
      overrides @ get_overrides csuper
    in
    List.iter
      begin fun (cn, {cl; cabstract; cmeths}) ->
        if not cabstract then begin
          let overrides = get_overrides cn in
          List.iter
            begin fun (cn, sign) ->
              if not (List.mem_assoc sign cmeths) then
                static_error cl (Printf.sprintf "This class must override method %s declared in class %s or must be declared abstract." (string_of_sign sign) cn) None
            end
            overrides
         end
      end
      classmap1
  end;
  
  if file_type path=Java && filepath = path then begin
    let rec check_spec_lemmas lemmas impl=
      match lemmas with
        [] when List.length impl=0-> ()
      | Func(l,Lemma(auto, trigger),tparams,rt,fn,arglist,nonghost_callers_only,ftype,contract,None,fb,vis)::rest ->
          if List.mem (fn,l) impl then
            let impl'= remove (fun (x,l0) -> x=fn && l=l0) impl in
            check_spec_lemmas rest impl'
          else
            static_error l "No implementation found for this lemma." None
    in
    check_spec_lemmas !spec_lemmas prototypes_implemented
  end;
  
  if file_type path=Java && filepath = path then begin
    let rec check_spec_classes classes meths_impl cons_impl=
      match classes with
        [] -> (match meths_impl with
            []-> ()
          | (n,lm0)::_ -> static_error lm0 ("Method not in specs: "^n) None
          )
      | Class(l,abstract,fin,cn,meths,fds,cons,super,inames,preds)::rest ->
          let check_meths meths meths_impl=
            let rec iter mlist meths_impl=
              match mlist with
                [] -> meths_impl
              | Meth(lm,gh,rt,n,ps,co,None,fb,v,abstract) as elem::rest ->
                if List.mem (n,lm) meths_impl then
                  let meths_impl'= remove (fun (x,l0) -> x=n && lm=l0) meths_impl in
                  iter rest meths_impl'
                else
                static_error lm "No implementation found for this method." None
            in
            iter meths meths_impl
          in
          let check_cons cons cons_impl=
            let rec iter clist cons_impl=
              match clist with
                [] -> cons_impl
              | Cons (lm,ps, co,None,v)::rest ->
                if List.mem (cn,lm) cons_impl then
                  let cons_impl'= remove (fun (x,l0) -> x=cn && lm=l0) cons_impl in
                  iter rest cons_impl'
                else
                static_error lm "No implementation found for this constructor." None
            in
            iter cons cons_impl
          in
          check_spec_classes rest (check_meths meths meths_impl) (check_cons cons cons_impl)
    in
    check_spec_classes !spec_classes !meths_impl !cons_impl
  end;
  
  (* Region: symbolic execution helpers *)
  
  let rec mark_if_local locals x =
    match locals with
      [] -> ()
    | (block, head) :: rest -> match try_assoc x head with None -> mark_if_local rest x | Some(addrtaken) -> addrtaken := true; (if(not (List.mem x !block)) then block := x :: (!block));
  in
  let rec expr_mark_addr_taken e locals = 
    match e with
      True _ | False _ | Null _ | Var(_, _, _) | IntLit(_, _, _) | RealLit _ | StringLit(_, _) | ClassLit(_) -> ()
    | Operation(_, _, es, _) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | AddressOf(_, Var(_, x, scope)) -> mark_if_local locals x
    | Read(_, e, _) -> expr_mark_addr_taken e locals
    | ArrayLengthExpr(_, e) -> expr_mark_addr_taken e locals
    | WRead(_, e, _, _, _, _, _, _) -> expr_mark_addr_taken e locals
    | ReadArray(_, e1, e2) -> (expr_mark_addr_taken e1 locals); (expr_mark_addr_taken e2 locals)
    | WReadArray(_, e1, _, e2) -> (expr_mark_addr_taken e1 locals); (expr_mark_addr_taken e2 locals)
    | Deref(_, e, _) -> expr_mark_addr_taken e locals
    | CallExpr(_, _, _, ps1, ps2, _) -> List.iter (fun pat -> pat_expr_mark_addr_taken pat locals) (ps1 @ ps2)
    | ExprCallExpr(_, e, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) (e :: es)
    | WFunPtrCall(_, _, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | WPureFunCall(_, _, _, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | WPureFunValueCall(_, e, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) (e :: es)
    | WFunCall(_, _, _, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | WMethodCall _ -> ()
    | NewArray _ -> ()
    | NewObject _ -> ()
    | NewArrayWithInitializer _ -> ()
    | IfExpr(_, e1, e2, e3) -> List.iter (fun e -> expr_mark_addr_taken e locals) [e1;e2;e3]
    | SwitchExpr(_, e, cls, dcl, _) -> List.iter (fun (SwitchExprClause(_, _, _, e)) -> expr_mark_addr_taken e locals) cls; (match dcl with None -> () | Some((_, e)) -> expr_mark_addr_taken e locals)
    | PredNameExpr _ -> ()
    | CastExpr(_, _, _, e) ->  expr_mark_addr_taken e locals
    | Upcast (e, _, _) -> expr_mark_addr_taken e locals
    | WidenedParameterArgument e -> expr_mark_addr_taken e locals
    | InstanceOfExpr(_, e, _) ->  expr_mark_addr_taken e locals
    | SizeofExpr _ -> ()
    | AddressOf(_, e) ->  expr_mark_addr_taken e locals
    | ProverTypeConversion(_, _, e) ->  expr_mark_addr_taken e locals
    | ArrayTypeExpr'(_, e) ->  expr_mark_addr_taken e locals
    | AssignExpr(_, e1, e2) ->  expr_mark_addr_taken e1 locals;  expr_mark_addr_taken e2 locals
    | AssignOpExpr(_, e1, _, e2, _, _, _) -> expr_mark_addr_taken e1 locals;  expr_mark_addr_taken e2 locals
    | InitializerList(_, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
  and pat_expr_mark_addr_taken pat locals = 
    match pat with
      LitPat(e) -> expr_mark_addr_taken e locals
    | _ -> ()
  in
  let rec ass_mark_addr_taken a locals = 
    match a with
      PointsTo(_, e, pat) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals;
    | WPointsTo(_, e, _, pat) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals;
    | PredAsn(_, _, _, pats1, pats2) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) (pats1 @ pats2)
    | WPredAsn(_, _, _, _, pats1, pats2) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) (pats1 @ pats2)
    | InstPredAsn(_, e, _, index, pats) -> expr_mark_addr_taken e locals; expr_mark_addr_taken index locals; List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats
    | WInstPredAsn(_, eopt, _, _, _, _, e, pats) -> 
      (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
      expr_mark_addr_taken e locals; 
      List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats
    | ExprAsn(_, e) -> expr_mark_addr_taken e locals; 
    | Sep(_, a1, a2) -> ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals
    | IfAsn(_, e, a1, a2) -> expr_mark_addr_taken e locals;  ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals
    | SwitchAsn(_, e, cls) -> expr_mark_addr_taken e locals;
        List.iter (fun (SwitchAsnClause(_, _, _, _, a)) -> ass_mark_addr_taken a locals) cls;
    | WSwitchAsn(_, e, i, cls) -> expr_mark_addr_taken e locals;
        List.iter (fun (SwitchAsnClause(_, _, _, _, a)) -> ass_mark_addr_taken a locals) cls;
    | EmpAsn _ -> ()
    | CoefAsn(_, pat, a) -> pat_expr_mark_addr_taken pat locals; ass_mark_addr_taken a locals;
  in
  let rec stmt_mark_addr_taken s locals cont =
    match s with
      DeclStmt(_, ds) ->
      let (block, mylocals)::rest = locals in
      ds |> List.iter begin fun (_, tp, x, e, _) ->
        begin match e with None -> () | Some(e) -> expr_mark_addr_taken e locals end;
        begin match tp with
          (* There is always an array chunk generated for a StaticArrayTypeExpr.
             Hence, we have to add this chunk to the list of locals to be freed
             at the end of the program block. *)
          StaticArrayTypeExpr (_, _, _) | StructTypeExpr (_, _) ->
          (* TODO: handle array initialisers *)
          block := x::!block
        | _ -> ()
        end
      end;
      cont ((block, List.map (fun (lx, tx, x, e, addrtaken) -> (x, addrtaken)) ds @ mylocals) :: rest)
    | BlockStmt(_, _, ss, _, locals_to_free) -> stmts_mark_addr_taken ss ((locals_to_free, []) :: locals) (fun _ -> cont locals)
    | ExprStmt(e) -> expr_mark_addr_taken e locals; cont locals
    | PureStmt(_, s) ->  stmt_mark_addr_taken s locals cont
    | NonpureStmt(_, _, s) -> stmt_mark_addr_taken s locals cont
    | IfStmt(l, e, ss1, ss2) -> 
        expr_mark_addr_taken e locals; 
        stmts_mark_addr_taken ss1 locals (fun locals -> stmts_mark_addr_taken ss2 locals (fun _ -> ())); cont locals
    | LabelStmt _ | GotoStmt _ | NoopStmt _ | Break _ | Throw _ | TryFinally _ | TryCatch _ -> cont locals
    | ReturnStmt(_, Some(e)) ->  expr_mark_addr_taken e locals; cont locals
    | ReturnStmt(_, None) -> cont locals
    | Assert(_, p) -> ass_mark_addr_taken p locals; cont locals
    | Leak(_, p) -> ass_mark_addr_taken p locals; cont locals
    | Open(_, eopt, _, _, pats1, pats2, patopt) | Close(_, eopt, _, _, pats1, pats2, patopt) ->
      (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
      List.iter (fun p -> pat_expr_mark_addr_taken p locals) (pats1 @ pats2);
      (match patopt with None -> () | Some(p) -> pat_expr_mark_addr_taken p locals); 
      cont locals
    | SwitchStmt(_, e, cls) -> expr_mark_addr_taken e locals; List.iter (fun cl -> match cl with SwitchStmtClause(_, e, ss) -> (expr_mark_addr_taken e locals); stmts_mark_addr_taken ss locals (fun _ -> ()); | SwitchStmtDefaultClause(_, ss) -> stmts_mark_addr_taken ss locals (fun _ -> ())) cls; cont locals
    | WhileStmt(_, e1, loopspecopt, e2, ss) -> 
        expr_mark_addr_taken e1 locals; 
        (match e2 with None -> () | Some(e2) -> expr_mark_addr_taken e2 locals);
        (match loopspecopt with 
          Some(LoopInv(a)) -> ass_mark_addr_taken a locals;
        | Some(LoopSpec(a1, a2)) -> ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals;
        | None -> ()
        );
        stmts_mark_addr_taken ss locals (fun _ -> cont locals); 
    | SplitFractionStmt(_, _, _, pats, eopt) -> 
        List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats;
        (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
        cont locals
    | MergeFractionsStmt(_, _, _, pats) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats;
    | CreateHandleStmt(_, _, _, e) -> expr_mark_addr_taken e locals; cont locals
    | DisposeBoxStmt(_, _, pats, clauses) -> 
        List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats;
        List.iter (fun (l, s, pats) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats) clauses;
        cont locals
    | InvariantStmt(_, a) -> ass_mark_addr_taken a locals; cont locals
    | _ -> cont locals
  and
  stmts_mark_addr_taken ss locals cont =
    match ss with
      [] -> cont locals
    | s :: ss -> stmt_mark_addr_taken s locals (fun locals -> stmts_mark_addr_taken ss locals cont)
  in
  
  (* locals whose address is taken in e *)
  
    let rec expr_address_taken e =
    let pat_address_taken pat =
      match pat with
        LitPat(e) -> expr_address_taken e
      | _ -> []
    in
    match e with
      True _ | False _ | Null _ | Var(_, _, _) | IntLit(_, _, _) | RealLit _ | StringLit(_, _) | ClassLit(_) -> []
    | Operation(_, _, es, _) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | Read(_, e, _) -> expr_address_taken e
    | ArrayLengthExpr(_, e) -> expr_address_taken e
    | WRead(_, e, _, _, _, _, _, _) -> expr_address_taken e
    | ReadArray(_, e1, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | WReadArray(_, e1, _, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | Deref(_, e, _) -> (expr_address_taken e)
    | CallExpr(_, _, _, ps1, ps2, _) -> List.flatten (List.map (fun pat -> pat_address_taken pat) (ps1 @ ps2))
    | ExprCallExpr(_, e, es) -> List.flatten (List.map (fun e -> expr_address_taken e) (e :: es))
    | WFunPtrCall(_, _, es) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | WPureFunCall(_, _, _, es) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | WPureFunValueCall(_, e, es) -> List.flatten (List.map (fun e -> expr_address_taken e) (e :: es))
    | WFunCall(_, _, _, es) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | WMethodCall _ -> []
    | NewArray _ -> []
    | NewObject _ -> []
    | NewArrayWithInitializer _ -> []
    | IfExpr(_, e1, e2, e3) -> (expr_address_taken e1) @ (expr_address_taken e2) @ (expr_address_taken e3)
    | SwitchExpr(_, e, cls, dcl, _) -> List.flatten (List.map (fun (SwitchExprClause(_, _, _, e)) -> expr_address_taken e) cls) @ (match dcl with None -> [] | Some((_, e)) -> expr_address_taken e)
    | PredNameExpr _ -> []
    | CastExpr(_, _, _, e) -> expr_address_taken e
    | Upcast (e, fromType, toType) -> expr_address_taken e
    | WidenedParameterArgument e -> expr_address_taken e
    | InstanceOfExpr(_, e, _) -> expr_address_taken e
    | SizeofExpr _ -> []
    | AddressOf(_, Var(_, x, scope)) -> [x]
    | AddressOf(_, e) -> expr_address_taken e
    | ProverTypeConversion(_, _, e) -> expr_address_taken e
    | ArrayTypeExpr'(_, e) -> expr_address_taken e
    | AssignExpr(_, e1, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | AssignOpExpr(_, e1, _, e2, _, _, _) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | InitializerList (_, es) -> flatmap expr_address_taken es
  in
  
  let rec stmt_address_taken s =
    (* incomplete: might miss &x expressions *)
    match s with
      PureStmt(_, s) -> stmt_address_taken s
    | NonpureStmt(_, _, s) -> stmt_address_taken s
    | DeclStmt(_, ds) -> List.flatten (List.map (fun (_, _, _, e, _) -> match e with None -> [] | Some(e) -> expr_address_taken e) ds)
    | ExprStmt(e) -> expr_address_taken e
    | IfStmt(_, e, ss1, ss2) -> (expr_address_taken e) @ (List.flatten (List.map (fun s -> stmt_address_taken s) (ss1 @ ss2)))
    | SwitchStmt(_, e, cls) -> (expr_address_taken e) @ (List.flatten (List.map (fun cl -> match cl with SwitchStmtClause(_, e, ss) -> (expr_address_taken e) @ (List.flatten (List.map (fun s -> stmt_address_taken s) ss)) | SwitchStmtDefaultClause(_, ss) -> (List.flatten (List.map (fun s -> stmt_address_taken s) ss))) cls))
    | Assert(_, p) -> []
    | Leak(_, p) -> []
    | Open _ | Close _ -> []
    | ReturnStmt(_, Some(e)) -> expr_address_taken e
    | ReturnStmt(_, None) -> []
    | WhileStmt(_, e1, loopspecopt, e2, ss) -> (expr_address_taken e1) @ (match e2 with None -> [] | Some(e2) -> expr_address_taken e2) @ (List.flatten (List.map (fun s -> stmt_address_taken s) ss))
    | BlockStmt(_, decls, ss, _, _) -> (List.flatten (List.map (fun s -> stmt_address_taken s) ss))
    | LabelStmt _ | GotoStmt _ | NoopStmt _ | Break _ | Throw _ | TryFinally _ | TryCatch _ -> []
    | _ -> []
  in
  
  let nonempty_pred_symbs = List.map (fun (_, (_, (_, _, _, _, symb, _))) -> symb) field_pred_map in
  
  let eval_non_pure_cps ev is_ghost_expr ((h, env) as state) env e cont =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg url -> assert_term t h env l msg url) in
    let read_field =
      (fun l t f -> read_field h env l t f),
      (fun l f -> read_static_field h env l f),
      (fun l p t -> deref_pointer h env l p t),
      (fun l a i -> read_array h env l a i)
    in
    eval_core_cps ev state assert_term (Some read_field) env e cont
  in
  
  let eval_non_pure is_ghost_expr h env e =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg url -> assert_term t h env l msg url) in
    let read_field =
      (fun l t f -> read_field h env l t f),
      (fun l f -> read_static_field h env l f),
      (fun l p t -> deref_pointer h env l p t),
      (fun l a i -> read_array h env l a i)
    in
    eval_core assert_term (Some read_field) env e
  in
  
  let assume_is_of_type l t tp cont =
    match tp with
      IntType -> assume (ctxt#mk_and (ctxt#mk_le min_int_term t) (ctxt#mk_le t max_int_term)) cont
    | PtrType _ -> assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) t) (ctxt#mk_le t max_ptr_term)) cont
    | ShortType _ -> assume (ctxt#mk_and (ctxt#mk_le min_short_term t) (ctxt#mk_le t max_short_term)) cont
    | Char _ -> assume (ctxt#mk_and (ctxt#mk_le min_char_term t) (ctxt#mk_le t max_char_term)) cont
    | UChar _ -> assume (ctxt#mk_and (ctxt#mk_le min_uchar_term t) (ctxt#mk_le t max_uchar_term)) cont
    | UintPtrType _ -> assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) t) (ctxt#mk_le t max_ptr_term)) cont
    | ObjType _ -> cont ()
    | _ -> static_error l (Printf.sprintf "Producing the limits of a variable of type '%s' is not yet supported." (string_of_type tp)) None
  in
  
  (* Region: verification of calls *)
  
  let verify_call funcmap eval_h l (pn, ilist) xo g targs pats (callee_tparams, tr, ps, funenv, pre, post, epost, v) pure leminfo sizemap h tparams tenv ghostenv env cont econt =
    let check_expr (pn,ilist) tparams tenv e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e tp in
    let eval_h h env pat cont =
      match pat with
        SrcPat (LitPat e) -> if not pure then check_ghost ghostenv l e; eval_h h env e cont
      | TermPat t -> cont h env t
    in
    let rec evhs h env pats cont =
      match pats with
        [] -> cont h env []
      | pat::pats -> eval_h h env pat (fun h env v -> evhs h env pats (fun h env vs -> cont h env (v::vs)))
    in 
    let tpenv =
      match zip callee_tparams targs with
        None -> static_error l "Incorrect number of type arguments." None
      | Some tpenv -> tpenv
    in
    let ys: string list = List.map (function (p, t) -> p) ps in
    let ws =
      match zip pats ps with
        None -> static_error l "Incorrect number of arguments." None
      | Some bs ->
        List.map
          (function
            (SrcPat (LitPat e), (x, t0)) ->
            let t = instantiate_type tpenv t0 in
            SrcPat (LitPat (box (check_expr_t (pn,ilist) tparams tenv e t) t t0))
          | (TermPat t, _) -> TermPat t
          ) bs
    in
    evhs h env ws $. fun h env ts ->
    let Some env' = zip ys ts in
    let _ = if file_type path = Java && match try_assoc "this" ps with Some ObjType _ -> true | _ -> false then 
      let this_term = List.assoc "this" env' in
      if not (ctxt#query (ctxt#mk_not (ctxt#mk_eq this_term (ctxt#mk_intlit 0)))) then
        assert_false h env l "Target of method call might be null." None
    in
    let cenv = [(current_thread_name, List.assoc current_thread_name env)] @ env' @ funenv in
    (fun cont -> if language = Java then with_context (Executing (h, env, l, "Verifying call")) cont else cont ()) $. fun () ->
    with_context PushSubcontext (fun () ->
      consume_asn rules tpenv h ghostenv cenv pre true real_unit (fun _ h ghostenv' env' chunk_size ->
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
                              Some (PredicateChunkSize k) when k < 0 -> ()
                            | _ ->
                              with_context (Executing (h, env', l, "Checking recursion termination")) (fun _ ->
                              assert_false h env l "Recursive lemma call does not decrease the heap (no full field chunks left) or the derivation depth of the first chunk and there is no inductive parameter." (Some "recursivelemmacall")
                            )
                          end
                      | Some x -> (
                          match try_assq (List.assoc x env') sizemap with
                            Some k when k < 0 -> ()
                          | _ ->
                            with_context (Executing (h, env', l, "Checking recursion termination")) (fun _ ->
                            assert_false h env l "Recursive lemma call does not decrease the heap (no full field chunks left) or the inductive parameter." None
                          )
                        )
                    )
                  else
                    static_error l "A lemma can call only preceding lemmas or itself." None
        in
        let r =
          match tr with
            None -> real_unit (* any term will do *)
          | Some t ->
            let symbol_name =
              match xo with
                None -> "result"
              | Some x -> x
            in
            get_unique_var_symb_ symbol_name t pure
        in
        let env'' = match tr with None -> env' | Some t -> update env' "result" r in
        (branch
          (fun () -> match epost with
              None -> ()
            | Some(epost) ->
                List.iter (fun (tp, post) -> produce_asn tpenv h ghostenv' env' post real_unit None None $. fun h _ _ ->
                  with_context PopSubcontext $. fun () ->
                  let e = get_unique_var_symb_ "excep" tp false in
                  (econt l h env tp e)
                )
                epost
          )
          (fun () ->
            produce_asn tpenv h ghostenv' env'' post real_unit None None $. fun h _ _ ->
            with_context PopSubcontext $. fun () ->
            cont h env r))
      )
    )
  in
  
  let funcnameterm_of funcmap fn =
    let FuncInfo (env, Some fterm, l, k, tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, _, _) = List.assoc fn funcmap in fterm
  in
  
  let default_value t =
    match t with
     Bool -> ctxt#mk_false
    | IntType|ShortType|Char|ObjType _|ArrayType _ -> ctxt#mk_intlit 0
    | _ -> get_unique_var_symb_non_ghost "value" t
  in

  
  let module LValues = struct
    type lvalue =
      Var of loc * string * ident_scope option ref
    | Field of
        loc
      * termnode option (* target struct instance or object; None if static *)
      * string (* parent, i.e. name of struct or class *)
      * string (* field name *)
      * type_ (* range, i.e. field type *)
      * constant_value option option ref
      * ghostness
      * termnode (* field symbol *)
    | ArrayElement of
        loc
      * termnode (* array *)
      * type_ (* element type *)
      * termnode (* index *)
    | Deref of (* C dereference operator, e.g. *p *)
        loc
      * termnode
      * type_ (* pointee type *)
  end in
  
  let rec verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt =
    let (envReadonly, heapReadonly) = readonly in
    let verify_expr readonly h env xo e cont = verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e (fun h env v -> cont h env v) econt in
    let check_expr (pn,ilist) tparams tenv e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e tp in
    let l = expr_loc e in
    let has_env_effects () = if language = CLang && envReadonly then static_error l "This potentially side-effecting expression is not supported in this position, because of C's unspecified evaluation order" (Some "illegalsideeffectingexpression") in
    let has_heap_effects () = if language = CLang && heapReadonly then static_error l "This potentially side-effecting expression is not supported in this position, because of C's unspecified evaluation order" (Some "illegalsideeffectingexpression") in
    let eval0 = eval in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure pure h env e in
    let eval_h h env e cont = verify_expr (true, true) h env None e cont in
    let eval_h_core ro h env e cont = if not pure then check_ghost ghostenv l e; verify_expr ro h env None e cont in
    let rec evhs h env es cont =
      match es with
        [] -> cont h env []
      | e::es -> eval_h h env e (fun h env v -> evhs h env es (fun h env vs -> cont h env (v::vs))) 
    in 
    let ev e = eval env e in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context." None
    in
    let vartp l x = 
      match try_assoc x tenv with
          None -> 
        begin
          match try_assoc' (pn, ilist) x globalmap with
            None -> static_error l ("No such variable: "^x) None
          | Some((l, tp, symbol, init)) -> (tp, Some(symbol))
        end 
      | Some tp -> (tp, None) 
    in
    let update_local_or_global h env tpx x symb w cont =
      match symb with
        None -> has_env_effects(); cont h (update env x w)
      | Some(symb) -> 
          has_heap_effects();
          let predSymb = pointee_pred_symb l tpx in
          get_points_to h symb predSymb l (fun h coef _ ->
            if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a global variable requires full permission." None;
            cont (Chunk ((predSymb, true), [], real_unit, [symb; w], None)::h) env)
    in
    let check_correct xo g targs args (lg, callee_tparams, tr, ps, funenv, pre, post, epost, v) cont =
      let eval_h = if List.length args = 1 then (fun h env e cont -> eval_h_core readonly h env e cont) else eval_h in
      verify_call funcmap eval_h l (pn, ilist) xo g targs (List.map (fun e -> SrcPat (LitPat e)) args) (callee_tparams, tr, ps, funenv, pre, post, epost, v) pure leminfo sizemap h tparams tenv ghostenv env cont econt
    in
    let new_array h env l elem_tp length elems =
      let at = get_unique_var_symb (match xo with None -> "array" | Some x -> x) (ArrayType elem_tp) in
      let (_, _, _, _, array_slice_symb, _) = List.assoc "java.lang.array_slice" predfammap in
      assume (ctxt#mk_not (ctxt#mk_eq at (ctxt#mk_intlit 0))) $. fun () ->
      assume (ctxt#mk_eq (ctxt#mk_app arraylength_symbol [at]) length) $. fun () ->
      cont (Chunk ((array_slice_symb, true), [elem_tp], real_unit, [at; ctxt#mk_intlit 0; length; elems], None)::h) env at
    in
    let lhs_to_lvalue h env lhs cont =
      match lhs with
        Var (l, x, scope) -> cont h env (LValues.Var (l, x, scope))
      | WRead (l, w, fparent, fname, tp, fstatic, fvalue, fghost) ->
        let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
        begin fun cont ->
          if fstatic then
            cont h env None
          else
            eval_h h env w (fun h env target -> cont h env (Some target))
        end $. fun h env target ->
        cont h env (LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb))
      | WReadArray (l, arr, elem_tp, i) ->
        eval_h h env arr $. fun h env arr ->
        eval_h h env i $. fun h env i ->
        cont h env (LValues.ArrayElement (l, arr, elem_tp, i))
      | Deref (l, w, pointeeType) ->
        eval_h h env w $. fun h env target ->
        cont h env (LValues.Deref (l, target, get !pointeeType))
      | _ -> static_error (expr_loc lhs) "Cannot assign to this expression." None
    in
    let read_lvalue h env lvalue cont =
      match lvalue with
        LValues.Var (l, x, scope) ->
        eval_h h env (Var (l, x, scope)) cont
      | LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb) ->
        begin match target with
          Some target ->
          consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 1) [TermPat target; dummypat] $. fun chunk h _ [_; value] _ _ _ _ ->
          cont (chunk::h) env value
        | None ->
          consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 0) [dummypat] $. fun chunk h _ [value] _ _ _ _ ->
          cont (chunk::h) env value
        end
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = Java ->
        let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
        consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit dummypat (Some 2) pats $. fun chunk h _ [_; _; value] _ _ _ _ ->
        cont (chunk::h) env value
      | LValues.Deref (l, target, pointeeType) ->
        let predSymb = pointee_pred_symb l pointeeType in
        consume_chunk rules h [] [] [] l (predSymb, true) [] real_unit dummypat (Some 1) [TermPat target; dummypat] $. fun chunk h _ [_; value] _ _ _ _ ->
        cont (chunk::h) env value
    in
    let rec write_lvalue h env lvalue value cont =
      match lvalue with
        LValues.Var (l, x, _) ->
        check_assign l x;
        let (tpx, symb) = vartp l x in
        update_local_or_global h env tpx x symb value cont
      | LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb) ->
        has_heap_effects();
        if pure && fghost = Real then static_error l "Cannot write in a pure context" None;
        let targets =
          match target with
            Some t -> [t]
          | None -> []
        in
        let pats = List.map (fun t -> TermPat t) targets @ [dummypat] in
        consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit (TermPat real_unit) (Some 1) pats $. fun _ h _ _ _ _ _ _ ->
        cont (Chunk ((f_symb, true), [], real_unit, targets @ [value], None)::h) env
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = Java ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        begin match try_update_java_array h env l arr i elem_tp value with
          None -> 
          let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
          consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit real_unit_pat (Some 2) pats $. fun _ h _ _ _ _ _ _ ->
          cont (Chunk ((array_element_symb(), true), [elem_tp], real_unit, [arr; i; value], None)::h) env
        | Some h ->
          cont h env
        end
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = CLang ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        let (_, _, _, _, c_array_symb, _) = List.assoc "array" predfammap in
        let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
        let predsym = pointee_pred_symb l elem_tp in
        let pats = [TermPat arr; SrcPat DummyPat; TermPat (sizeof l elem_tp); TermPat predsym; SrcPat DummyPat] in
        consume_chunk rules h [] [] [] l (c_array_symb, true) [elem_tp] real_unit real_unit_pat (Some 4) pats $. fun _ h _ [a; n; size; q; vs] _ _ _ _ ->
        let term = ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) i) (ctxt#mk_lt i n) in
        assert_term term h env l ("Could not prove that index is in bounds of the array: " ^ (ctxt#pprint term)) None;
        let updated = mk_app update_symb [i; apply_conversion (provertype_of_type elem_tp) ProverInductive value; vs] in
        cont (Chunk ((c_array_symb, true), [elem_tp], real_unit, [a; n; size; q; updated], None) :: h) env
      | LValues.Deref (l, target, pointeeType) ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        let predSymb = pointee_pred_symb l pointeeType in
        consume_chunk rules h [] [] [] l (predSymb, true) [] real_unit dummypat (Some 1) [TermPat target; dummypat] $. fun _ h coef _ _ _ _ _ ->
        if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a memory location requires full permission." None;
        cont (Chunk ((predSymb, true), [], real_unit, [target; value], None)::h) env
    in
    let rec execute_assign_op_expr h env lhs get_values cont =
      lhs_to_lvalue h env lhs $. fun h env lvalue ->
      read_lvalue h env lvalue $. fun h env v1 ->
      get_values h env v1 $. fun h env result_value new_value ->
      write_lvalue h env lvalue new_value $. fun h env ->
      cont h env result_value
    in
    match e with
    | CastExpr (lc, false, ManifestTypeExpr (_, tp), (WFunCall (l, "malloc", [], [SizeofExpr (ls, StructTypeExpr (lt, tn))]) as e)) ->
      expect_type lc (PtrType (StructType tn)) tp;
      verify_expr readonly h env xo e cont 
    | WFunCall (l, "malloc", [], [SizeofExpr (ls, te)]) ->
      if pure then static_error l "Cannot call a non-pure function from a pure context." None;
      let t = check_pure_type (pn,ilist) tparams te in
      let resultType = PtrType t in
      let result = get_unique_var_symb (match xo with None -> (match t with StructType tn -> tn | _ -> "address") | Some x -> x) resultType in
      let cont h = cont h env result in
      branch
        begin fun () ->
          assume_eq result (ctxt#mk_intlit 0) $. fun () ->
          cont h
        end
        begin fun () ->
          assume_neq result (ctxt#mk_intlit 0) $. fun () ->
          produce_c_object l real_unit result t None true h $. fun h ->
          match t with
            StructType sn ->
            let (_, (_, _, _, _, malloc_block_symb, _)) = List.assoc sn malloc_block_pred_map in
            cont (Chunk ((malloc_block_symb, true), [], real_unit, [result], None)::h)
          | _ ->
            cont (Chunk ((get_pred_symb "malloc_block", true), [], real_unit, [result; sizeof l t], None)::h)
        end
    | WFunPtrCall (l, g, args) ->
      let (PtrType (FuncType ftn)) = List.assoc g tenv in
      has_heap_effects ();
      let fterm = List.assoc g env in
      let (_, gh, fttparams, rt, ftxmap, xmap, pre, post, ft_predfammaps) = List.assoc ftn functypemap in
      if pure && gh = Real then static_error l "Cannot call regular function pointer in a pure context." None;
      let check_call targs h args0 cont =
        verify_call funcmap eval_h l (pn, ilist) xo None targs (TermPat fterm::List.map (fun arg -> TermPat arg) args0 @ List.map (fun e -> SrcPat (LitPat e)) args) (fttparams, rt, (("this", PtrType Void)::ftxmap @ xmap), [], pre, post, None, Public) pure leminfo sizemap h tparams tenv ghostenv env cont (fun _ _ _ _ -> assert false)
      in
      begin
        match gh with
          Real when ftxmap = [] ->
          let (lg, _, _, _, isfuncsymb) = List.assoc ("is_" ^ ftn) purefuncmap in
          let phi = mk_app isfuncsymb [fterm] in
          assert_term phi h env l ("Could not prove is_" ^ ftn ^ "(" ^ g ^ ")") None;
          check_call [] h [] cont
        | Real ->
          let [(_, (_, _, _, _, predsymb, inputParamCount))] = ft_predfammaps in
          let pats = TermPat fterm::List.map (fun _ -> SrcPat DummyPat) ftxmap in
          consume_chunk rules h [] [] [] l (predsymb, true) [] real_unit dummypat inputParamCount pats $. fun _ h coef (_::args) _ _ _ _ ->
          check_call [] h args $. fun h env retval ->
          cont (Chunk ((predsymb, true), [], coef, fterm::args, None)::h) env retval
        | Ghost ->
          let [(_, (_, _, _, _, predsymb, inputParamCount))] = ft_predfammaps in
          let targs = List.map (fun _ -> InferredType (ref None)) fttparams in
          let pats = TermPat fterm::List.map (fun _ -> SrcPat DummyPat) ftxmap in
          consume_chunk rules h [] [] [] l (predsymb, true) targs real_unit dummypat inputParamCount pats $. fun chunk h coef (_::args) _ _ _ _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk required." None;
          let targs = List.map unfold_inferred_type targs in
          check_call targs h args $. fun h env retval ->
          cont (chunk::h) env retval
      end
    | NewObject (l, cn, args) ->
      if pure then static_error l "Object creation is not allowed in a pure context" None;
      let {cctors} = List.assoc cn classmap in
      let args' = List.map (fun e -> check_expr (pn,ilist) tparams tenv e) args in
      let argtps = List.map snd args' in
      let consmap' = List.filter (fun (sign, _) -> is_assignable_to_sign argtps sign) cctors in
      begin match consmap' with
        [] -> static_error l "No matching constructor" None
      | [(sign, (lm, xmap, pre, pre_tenv, post, epost, ss, v))] ->
        let obj = get_unique_var_symb (match xo with None -> "object" | Some x -> x) (ObjType cn) in
        assume_neq obj (ctxt#mk_intlit 0) $. fun () ->
        assume_eq (ctxt#mk_app get_class_symbol [obj]) (List.assoc cn classterms) $. fun () ->
        check_correct None None [] args (lm, [], None, xmap, ["this", obj], pre, post, Some(epost), Static) (fun h env _ -> cont h env obj)
      | _ -> static_error l "Multiple matching overloads" None
      end
    | WMethodCall (l, tn, m, pts, args, fb) when m <> "getClass" ->
      let (lm, gh, rt, xmap, pre, post, epost, fb', v) =
        match try_assoc tn classmap with
          Some {cmeths} ->
          let (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract) = List.assoc (m, pts) cmeths in
          (lm, gh, rt, xmap, pre_dyn, post_dyn, epost_dyn, fb, v)
        | _ ->
          let InterfaceInfo (_, _, methods, _, _) = List.assoc tn interfmap in
          let (lm, gh, rt, xmap, pre, pre_tenv, post, epost, v, abstract) = List.assoc (m, pts) methods in
          (lm, gh, rt, xmap, pre, post, epost, Instance, v)
      in
      if gh = Real && pure then static_error l "Method call is not allowed in a pure context" None;
      if gh = Ghost then begin
        if not pure then static_error l "A lemma method call is not allowed in a non-pure context." None;
        if leminfo <> None then static_error l "Lemma method calls in lemmas are currently not supported (for termination reasons)." None
      end;
      check_correct xo None [] args (lm, [], rt, xmap, [], pre, post, Some epost, v) cont
    | WSuperMethodCall(l, m, args, (lm, gh, rt, xmap, pre, post, epost, v)) ->
      if gh = Real && pure then static_error l "Method call is not allowed in a pure context" None;
      if gh = Ghost then begin
        if not pure then static_error l "A lemma method call is not allowed in a non-pure context." None;
        if leminfo <> None then static_error l "Lemma method calls in lemmas are currently not supported (for termination reasons)." None
      end;
      check_correct None None [] args (lm, [], rt, xmap, [], pre, post, Some epost, v) cont
    | WFunCall (l, g, targs, es) ->
      let FuncInfo (funenv, fterm, lg, k, tparams, tr, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, fbf, v) = List.assoc g funcmap in
      has_heap_effects ();
      if body = None then register_prototype_used lg g;
      if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." None;
      if not pure && is_lemma k then static_error l "Cannot call lemma functions in a non-pure context." None;
      if nonghost_callers_only && leminfo <> None then static_error l "A lemma function marked nonghost_callers_only cannot be called from a lemma function." None;
      check_correct xo (Some g) targs es (lg, tparams, tr, ps, funenv, pre, post, None, v) cont
    | NewArray(l, tp, e) ->
      let elem_tp = check_pure_type (pn,ilist) tparams tp in
      let w = check_expr_t (pn,ilist) tparams tenv e IntType in
      eval_h h env w $. fun h env lv ->
      if not (ctxt#query (ctxt#mk_le (ctxt#mk_intlit 0) lv)) then assert_false h env l "array length might be negative" None;
      let elems = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
      let (_, _, _, _, all_eq_symb) = List.assoc "all_eq" purefuncmap in
      let (_, _, _, _, length_symb) = List.assoc "length" purefuncmap in
      assume_eq (mk_app length_symb [elems]) lv $. fun () ->
        assume (mk_app all_eq_symb [elems; ctxt#mk_boxed_int (ctxt#mk_intlit 0)]) $. fun () ->
          new_array h env l elem_tp lv elems
    | NewArrayWithInitializer(l, tp, es) ->
      let elem_tp = check_pure_type (pn,ilist) tparams tp in
      let ws = List.map (fun e -> check_expr_t (pn,ilist) tparams tenv e elem_tp) es in
      evhs h env ws $. fun h env vs ->
      let elems = mk_list elem_tp vs in
      let lv = ctxt#mk_intlit (List.length vs) in
      new_array h env l elem_tp lv elems
    | StringLit (l, s)->
      begin match file_type path with
        Java ->
        let value = get_unique_var_symb "stringLiteral" (ObjType "java.lang.String") in
        assume_neq value (ctxt#mk_intlit 0) (fun () ->
          cont h env value
        )
      | _ ->
        if unloadable then static_error l "The use of string literals as expressions in unloadable modules is not supported. Put the string literal in a named global array variable instead." None;
        let (_, _, _, _, chars_symb, _) = List.assoc "chars" predfammap in
        let (_, _, _, _, mem_symb) = List.assoc "mem" purefuncmap in
        let cs = get_unique_var_symb "stringLiteralChars" (InductiveType ("list", [Char])) in
        let value = get_unique_var_symb "stringLiteral" (PtrType Char) in
        let coef = get_dummy_frac_term () in
        assume (mk_app mem_symb [ctxt#mk_boxed_int (ctxt#mk_intlit 0); cs]) (fun () ->     (* mem(0, cs) == true *)
          assume (ctxt#mk_not (ctxt#mk_eq value (ctxt#mk_intlit 0))) (fun () ->
            assume (ctxt#mk_eq (mk_char_list_of_c_string (String.length s + 1) s) cs) (fun () ->
              cont (Chunk ((chars_symb, true), [], coef, [value; cs], None)::h) env value
            )
          )
        )
      end
    | Operation (l, Add, [e1; e2], t) when !t = Some [ObjType "java.lang.String"; ObjType "java.lang.String"] ->
      eval_h h env e1 $. fun h env v1 ->
      eval_h h env e2 $. fun h env v2 ->
      let value = get_unique_var_symb "string" (ObjType "java.lang.String") in
      assume_neq value (ctxt#mk_intlit 0) $. fun () ->
      cont h env value
    | WRead (l, e, fparent, fname, frange, false (* is static? *), fvalue, fghost) ->
      eval_h h env e $. fun h env t ->
      begin match frange with
        StaticArrayType (elemTp, elemCount) ->
        cont h env (field_address l t fparent fname)
      | _ ->
      let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
      begin match lookup_points_to_chunk_core h f_symb t with
        None -> (* Try the heavyweight approach; this might trigger a rule (i.e. an auto-open or auto-close) and rewrite the heap. *)
        get_points_to h t f_symb l $. fun h coef v ->
        cont (Chunk ((f_symb, true), [], coef, [t; v], None)::h) env v
      | Some v -> cont h env v
      end
      end
    | WRead (l, _, fparent, fname, frange, true (* is static? *), fvalue, fghost) when ! fvalue = None || ! fvalue = Some None->
      let (_, (_, _, _, _, f_symb, _)) = List.assoc (fparent, fname) field_pred_map in
      consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 0) [dummypat] (fun chunk h coef [field_value] size ghostenv _ _ ->
        cont (chunk :: h) env field_value)
    | WReadArray (l, arr, elem_tp, i) when language = Java ->
      eval_h h env arr $. fun h env arr ->
      eval_h h env i $. fun h env i ->
      begin match try_read_java_array h env l arr i elem_tp with
        None -> 
          let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
          consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit (SrcPat DummyPat) (Some 2) pats $. fun _ h coef [_; _; elem] _ _ _ _ ->
          let elem_tp = unfold_inferred_type elem_tp in
          cont (Chunk ((array_element_symb(), true), [elem_tp], coef, [arr; i; elem], None)::h) env elem
      | Some (v) -> 
        if not pure then assume_bounds v elem_tp;
        cont h env v
      end
    | WReadArray (l, arr, elem_tp, i) when language = CLang ->
      eval_h h env arr $. fun h env arr ->
      eval_h h env i $. fun h env i ->
      cont h env (read_c_array h env l arr i elem_tp)
    | Operation (l, Not, [e], ts) -> eval_h_core readonly h env e (fun h env v -> cont h env (ctxt#mk_not v))
    | Operation (l, Eq, [e1; e2], ts) ->
      eval_h h env e1 (fun h env v1 -> eval_h h env e2 (fun h env v2 -> cont h env (ctxt#mk_eq v1 v2)))
    | Operation (l, Neq, [e1; e2], ts) ->
      eval_h h env e1 (fun h env v1 -> eval_h h env e2 (fun h env v2 -> cont h env (ctxt#mk_not (ctxt#mk_eq v1 v2))))
    | Operation (l, And, [e1; e2], ts) ->
      eval_h h env e1 $. fun h env v1 ->
      branch
        (fun () -> assume v1 (fun () -> eval_h h env e2 cont))
        (fun () -> assume (ctxt#mk_not v1) (fun () -> cont h env ctxt#mk_false))
    | Operation (l, Or, [e1; e2], ts) -> 
      eval_h h env e1 $. fun h env v1 ->
      branch
        (fun () -> assume v1 (fun () -> cont h env ctxt#mk_true))
        (fun () -> assume (ctxt#mk_not v1) (fun () -> eval_h h env e2 cont))
    | IfExpr (l, con, e1, e2) ->
      eval_h_core readonly h env con $. fun h env v ->
      branch
        (fun () -> assume v (fun () -> eval_h_core readonly h env e1 cont))
        (fun () -> assume (ctxt#mk_not v) (fun () -> eval_h_core readonly h env e2 cont))
    | AssignOpExpr(l, lhs, op, rhs, postOp, ts, lhs_type) when !ts = Some [ObjType "java.lang.String"; ObjType "java.lang.String"] ->
      eval_h h env lhs $. fun h env v1 ->
      let get_values = (fun h env v1 cont ->
        eval_h h env rhs $. fun h env v2 ->
        let new_value = get_unique_var_symb "string" (ObjType "java.lang.String") in
        assume_neq new_value (ctxt#mk_intlit 0) $. fun () ->
        let result_value = if postOp then v1 else new_value in
        cont h env result_value new_value
      )
      in
      execute_assign_op_expr h env lhs get_values cont
    | AssignOpExpr(l, lhs, ((And | Or | Xor) as op), rhs, postOp, ts, lhs_type) as aoe ->
      assert(match !lhs_type with None -> false | _ -> true);
      let get_values = (fun h env v1 cont -> eval_h h env rhs (fun h env v2 ->
          let new_value = 
            match op with
              And -> ctxt#mk_and v1 v2
            | Or -> ctxt#mk_or v1 v2
            | Xor -> (ctxt#mk_and (ctxt#mk_or v1 v2) (ctxt#mk_not (ctxt#mk_and v1 v2)))
          in
          let result_value = if postOp then v1 else new_value in
          cont h env result_value new_value
      ))
      in
      execute_assign_op_expr h env lhs get_values cont
    | AssignOpExpr(l, lhs, ((Add | Sub | Mul | ShiftLeft | ShiftRight | Div | Mod | BitAnd | BitOr | BitXor) as op), rhs, postOp, ts, lhs_type) as aoe ->
        let Some [t1; t2] = ! ts in
        let Some lhs_type = ! lhs_type in
        let get_values = (fun h env v1 cont -> eval_h h env rhs (fun h env v2 ->
          let check_overflow min t max =
            (if not disable_overflow_check && not pure then begin
            assert_term (ctxt#mk_le min t) h env l "Potential arithmetic underflow." (Some "potentialarithmeticunderflow");
            assert_term (ctxt#mk_le t max) h env l "Potential arithmetic overflow." (Some "potentialarithmeticoverflow");
            end
            );
            t
          in
          let (min_term, max_term) = 
            match lhs_type with
              Char -> (min_char_term, max_char_term)
            | ShortType -> (min_short_term, max_short_term)
            | IntType -> (min_int_term, max_int_term)
            | UintPtrType -> (min_uint_term, max_uint_term)
            | PtrType t -> ((ctxt#mk_intlit 0), max_ptr_term)
            | _ -> (min_int_term, max_int_term)
          in
          let bounds = if pure then (* in ghost code, where integer types do not imply limits *) None else 
            match !ts with
              Some ([UintPtrType; _] | [_; UintPtrType]) -> Some (int_zero_term, max_ptr_term)
            | Some ([IntType; _] | [_; IntType]) -> Some (min_int_term, max_int_term)
            | Some ([ShortType; _] | [_; ShortType]) -> Some (min_short_term, max_short_term)
            | Some ([Char; _] | [_; Char]) -> Some (min_char_term, max_char_term)
            | _ -> None
          in
          let new_value = 
          begin match op with
            Add ->
            begin match !ts with
              (Some [IntType; IntType]) | (Some [ShortType; ShortType]) | (Some [Char; Char]) | (Some [UintPtrType; UintPtrType]) ->
              check_overflow min_term (ctxt#mk_add v1 v2) max_term
            | Some [PtrType t; IntType] ->
              let n = sizeof l t in
              check_overflow min_term (ctxt#mk_add v1 (ctxt#mk_mul n v2)) max_term
            | Some [RealType; RealType] ->
              ctxt#mk_real_add v1 v2
            | _ -> static_error l "CompoundAssignment not supported for the given types." None
            end
          | Sub ->
            begin match !ts with
              (Some [IntType; IntType]) | (Some [ShortType; ShortType]) | (Some [Char; Char]) | (Some [UintPtrType; UintPtrType])->
              check_overflow min_term (ctxt#mk_sub v1 v2) max_term
            | Some [PtrType t; IntType] ->
              let n = sizeof l t in
              check_overflow min_term (ctxt#mk_sub v1 (ctxt#mk_mul n v2)) max_term
            | Some [RealType; RealType] ->
              ctxt#mk_real_sub v1 v2
            | _ -> static_error l "CompoundAssignment not supported for the given types." None
            end
          | Mul ->
            begin match !ts with
              (Some [IntType; IntType]) | (Some [ShortType; ShortType]) | (Some [Char; Char]) ->
              check_overflow min_term (ctxt#mk_mul v1 v2) max_term
            | Some [RealType; RealType] ->
              ctxt#mk_real_mul v1 v2
            | _ -> static_error l "CompoundAssignment not supported for the given types." None
            end
          | Div ->
            assert_term (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) h env l "Divisor might be zero." None;
            let res = (ctxt#mk_div v1 v2) in
            begin match lhs_type with
              IntType -> res
            | _ -> check_overflow min_term res max_term
            end
          | Mod -> (ctxt#mk_mod v1 v2)
          | BitAnd | BitOr | BitXor ->
            let symb = match op with
              BitAnd -> bitwise_and_symbol
            | BitXor -> bitwise_xor_symbol
            | BitOr -> bitwise_or_symbol
            in
            let app = ctxt#mk_app symb [v1;v2] in
            begin match bounds with
              None -> ()
            | Some(min_term, max_term) -> 
              ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_term app) (ctxt#mk_le app max_term)));
            end;  
            begin match lhs_type with
              IntType -> app
            | _ -> check_overflow min_term app max_term
            end 
          | ShiftLeft when !ts = Some [IntType; IntType] ->
            let app = ctxt#mk_app shiftleft_int32_symbol [v1;v2] in
            begin match bounds with
              None -> ()
            | Some(min_term, max_term) -> 
              ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_int_term app) (ctxt#mk_le app max_int_term)));
            end; 
            begin match lhs_type with
              IntType -> app
            | _ -> check_overflow min_term app max_term
            end
          | ShiftRight -> ctxt#mk_app shiftright_symbol [v1;v2]
          | _ -> static_error l "Compound assignment not supported for this operator yet." None
          end
          in
          let result_value = if postOp then v1 else new_value in
          cont h env result_value new_value))
        in
        execute_assign_op_expr h env lhs get_values cont
    | AssignExpr (l, lhs, rhs) ->
      lhs_to_lvalue h env lhs $. fun h env lvalue ->
      let varName = match lhs with Var (_, x, _) -> Some x | _ -> None in
      let rhsHeapReadOnly =
        match (lhs, rhs) with
          (Var (_, _, _), WFunCall (_, _, _, _)) -> false (* Is this OK when the variable is a global? *)
        | (Var (_, _, scope), _) when !scope = Some LocalVar -> false
        | _ -> true
      in
      verify_expr (true, rhsHeapReadOnly) h env varName rhs $. fun h env vrhs ->
      write_lvalue h env lvalue vrhs $. fun h env ->
      cont h env vrhs
    | e ->
      eval_non_pure_cps (fun (h, env) e cont -> eval_h h env e (fun h env t -> cont (h, env) t)) pure (h, env) env e (fun (h, env) v -> cont h env v)
  in
  
  (* Region: verification of statements *)
  
  let verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt =
    verify_expr (readonly, readonly) (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt
  in
  
  let rec verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt =
    stats#stmtExec;
    let l = stmt_loc s in
    let free_locals closeBraceLoc h tenv env locals cont =
      let rec free_locals_core h locals =
        match locals with
          [] -> cont h env
        | x::locals ->
          match try_assoc x env with
            None ->
            free_locals_core h locals
          | Some addr ->
            match List.assoc x tenv with
              StaticArrayType (elemTp, elemCount) as t ->
              consume_c_object closeBraceLoc addr t h $. fun h ->
              free_locals_core h locals
            | RefType t -> (* free locals of which the address is taken *)
              consume_c_object closeBraceLoc addr t h $. fun h ->
              free_locals_core h locals
      in
      match locals with
        [] -> cont h env
      | _ -> with_context (Executing (h, env, closeBraceLoc, "Freeing locals.")) (fun _ -> free_locals_core h locals)
    in
    let rec check_block_declarations ss =
      let rec check_after_initial_declarations ss = 
        match ss with
          [] -> ()
        | DeclStmt(l, ds) :: rest -> 
          ds |> List.iter begin fun (_, _, _, _, addresstaken) ->
              if !addresstaken then
                static_error l "A local variable whose address is taken must be declared at the start of a block." None
            end;
          check_after_initial_declarations rest
        | _ :: rest -> check_after_initial_declarations rest
      in
      match ss with
        [] -> ()
      | PureStmt _ :: rest -> check_block_declarations rest
      | DeclStmt _ :: rest -> check_block_declarations rest
      | _ :: rest -> check_after_initial_declarations rest
    in
    if !verbosity >= 1 then printff "%10.6fs: %s: Executing statement\n" (Perf.time ()) (string_of_loc l);
    check_breakpoint h env l;
    let check_expr (pn,ilist) tparams tenv e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e tp in
    let eval0 = eval in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure pure h env e in
    let eval_h_core sideeffectfree h env e cont =
      if not pure then check_ghost ghostenv l e;
      verify_expr sideeffectfree (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env None e cont econt
    in
    let eval_h h env e cont =
      eval_h_core true h env e cont
    in
    let eval_h_nonpure h env e cont =
      eval_h_core false h env e cont
    in
    let rec evhs h env es cont =
      match es with
        [] -> cont h env []
      | e::es -> eval_h h env e (fun h env v -> evhs h env es (fun h env vs -> cont h env (v::vs)))
    in 
    let ev e = eval env e in
    let cont= tcont sizemap tenv ghostenv
    in
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context." None
    in
    let vartp l x = 
      match try_assoc x tenv with
          None -> 
        begin
          match try_assoc' (pn, ilist) x globalmap with
            None -> static_error l ("No such variable: "^x) None
          | Some((l, tp, symbol, init)) -> (tp, Some(symbol))
        end 
      | Some tp -> (tp, None) 
    in
    let update_local_or_global h env tpx x symb w cont =
      match symb with
        None -> cont h (update env x w)
      | Some(symb) -> 
          let predSymb = pointee_pred_symb l tpx in
          get_points_to h symb predSymb l (fun h coef _ ->
            if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a global variable requires full permission." None;
            cont (Chunk ((predSymb, true), [], real_unit, [symb; w], None)::h) env)
    in
    let verify_expr readonly h env xo e cont =
      if not pure then check_ghost ghostenv l e;
      verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont
    in
    let verify_produce_function_pointer_chunk_stmt stmt_ghostness l fpe ftclause_opt scope_opt =
      if not pure then static_error l "This construct is not allowed in a non-pure context." None;
      let (lfn, fn) =
        match fpe with
          Var (lfn, x, _) -> (lfn, x)
        | _ -> static_error (expr_loc fpe) "Function name expected" None
      in
      match resolve (pn,ilist) l fn funcmap with
        None -> static_error l "No such function." None
      | Some (fn, FuncInfo (funenv, Some fterm, lf, k, f_tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body',fb,v)) ->
        if stmt_ghostness = Ghost && not (is_lemma k) then static_error l "Not a lemma function." None;
        if stmt_ghostness = Real && k <> Regular then static_error l "Regular function expected." None;
        if f_tparams <> [] then static_error l "Taking the address of a function with type parameters is not yet supported." None;
        if body' = None then register_prototype_used lf fn;
        if stmt_ghostness = Ghost then begin
          match leminfo with
            None -> ()
          | Some (lems, g0, indinfo) ->
            if not (List.mem fn lems) then static_error l "Function pointer chunks can only be produced for preceding lemmas." None;
            if scope_opt = None then static_error l "produce_lemma_function_pointer_chunk statement must have a body." None
        end;
        let (ftn, ft_predfammaps, fttargs, ftargs) =
          match ftclause_opt with
            None ->
            begin match functype_opt with
              None -> static_error l "Function does not implement a function type." None
            | Some (ftn, ft_predfammaps, fttargs, ftargs) ->
              if ftargs <> [] then static_error l "Function header must not specify function type arguments." None;
              (ftn, ft_predfammaps, fttargs, [])
            end
          | Some (ftn, fttargs, args, params, openBraceLoc, ss, closeBraceLoc) ->
            let (rt1, xmap1, pre1, post1) = (rt, ps, pre, post) in
            begin match resolve (pn,ilist) l ftn functypemap with
              None -> static_error l "No such function type" None
            | Some (ftn, (lft, gh, fttparams, rt, ftxmap, xmap, pre, post, ft_predfammaps)) ->
              begin match stmt_ghostness with
                Real -> if gh <> Real || ftxmap = [] then static_error l "A produce_function_pointer_chunk statement may be used only for parameterized function types." None
              | Ghost -> if gh <> Ghost then static_error l "Lemma function pointer type expected." None
              end;
              begin match (rt, rt1) with
                (None, _) -> ()
              | (Some t, Some t1) -> expect_type_core l "Function return type: " t1 t
              | _ -> static_error l "Return type mismatch: Function does not return a value" None
              end;
              let fttargs = List.map (check_pure_type (pn,ilist) tparams) fttargs in
              let tpenv =
                match zip fttparams fttargs with
                  None -> static_error l "Incorrect number of function type type arguments." None
                | Some bs -> bs
              in
              let xmap =
                match zip xmap xmap1 with
                  None -> static_error l "Function type parameter count does not match function parameter count" None
                | Some bs ->
                  List.map
                    begin fun ((x, tp0), (x1, tp1)) ->
                      let tp = instantiate_type tpenv tp0 in
                      expect_type_core l (Printf.sprintf "The types of function parameter '%s' and function type parameter '%s' do not match: " x1 x) tp tp1;
                      (x, tp, tp0, x1, tp1)
                    end
                  bs
              in
              let ftargenv =
                match zip ftxmap args with
                  None -> static_error l "Incorrect number of function pointer chunk arguments" None
                | Some bs ->
                  List.map
                    begin fun ((x, tp), e) ->
                      let w = check_expr_t (pn,ilist) tparams tenv e (instantiate_type tpenv tp) in
                      (x, ev w)
                    end
                    bs
              in
              let fparams =
                match zip params xmap with
                  None -> static_error l "Incorrect number of parameter names" None
                | Some bs ->
                  List.map
                    begin fun ((lx, x), (x0, tp, tp0, x1, tp1)) ->
                      if List.mem_assoc x tenv then static_error lx "Parameter name hides existing local variable" None;
                      let t = get_unique_var_symb x tp in
                      (x, x0, tp, t, prover_convert_term t tp tp0, x1, tp1)
                    end
                    bs
              in
              let (ss_before, callLoc, resultvar, ss_after) =
                let rec iter ss_before ss_after =
                  match ss_after with
                    [] -> static_error l "'call();' statement expected" None
                  | ExprStmt (CallExpr (lc, "call", [], [], [], Static))::ss_after -> (List.rev ss_before, lc, None, ss_after)
                  | DeclStmt (ld, [lx, tx, x, Some(CallExpr (lc, "call", [], [], [], Static)), _])::ss_after ->
                    if List.mem_assoc x tenv then static_error ld "Variable hides existing variable" None;
                    let t = check_pure_type (pn,ilist) tparams tx in
                    begin match rt1 with
                      None -> static_error ld "Function does not return a value" None
                    | Some rt1 ->
                      expect_type ld rt1 t;
                      (List.rev ss_before, lc, Some (x, t), ss_after)
                    end
                  | s::ss_after -> iter (s::ss_before) ss_after
                in
                iter [] ss
              in
              begin
                let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
                let h = [] in
                with_context (Executing (h, [], openBraceLoc, "Producing function type precondition")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                let pre_env = [("this", fterm)] @ currentThreadEnv @ ftargenv @ List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x0, t0)) fparams in
                produce_asn tpenv h [] pre_env pre real_unit None None $. fun h _ ft_env ->
                with_context PopSubcontext $. fun () ->
                let tenv = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x, tp)) fparams @ tenv in
                let ghostenv = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> x) fparams @ ghostenv in
                let env = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x, t)) fparams @ env in
                let lblenv = [] in
                let pure = true in
                let return_cont h tenv env t = assert_false h [] l "You cannot return out of a produce_function_pointer_chunk statement" None in
                let econt _ h env texcep excep = assert_false h [] l "You cannot throw an exception from a produce_function_pointer_chunk statement" None in
                begin fun tcont ->
                  verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss_before tcont return_cont econt
                end $. fun sizemap tenv ghostenv h env ->
                with_context (Executing (h, env, callLoc, "Verifying function call")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                let pre1_env = currentThreadEnv @ List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x1, t)) fparams @ funenv in
                consume_asn rules [] h [] pre1_env pre1 true real_unit $. fun _ h _ f_env _ ->
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
                produce_asn [] h [] f_env post1 real_unit None None $. fun h _ _ ->
                with_context PopSubcontext $. fun () ->
                begin fun tcont ->
                  verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss_after tcont return_cont econt
                end $. fun sizemap tenv ghostenv h env ->
                with_context (Executing (h, env, closeBraceLoc, "Consuming function type postcondition")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                consume_asn rules tpenv h [] ft_env post true real_unit $. fun _ h _ _ _ ->
                with_context PopSubcontext $. fun () ->
                check_leaks h [] closeBraceLoc "produce_function_pointer_chunk body leaks heap chunks"
              end;
              (ftn, ft_predfammaps, fttargs, List.map snd ftargenv)
            end
        in
        let [(_, (_, _, _, _, symb, _))] = ft_predfammaps in
        let coef = match stmt_ghostness with Real -> get_dummy_frac_term () | Ghost -> real_unit in
        let h = Chunk ((symb, true), fttargs, coef, fterm::ftargs, None)::h in
        match scope_opt with
          None -> cont h env
        | Some s ->
          let consume_chunk h cont =
            with_context (Executing (h, [], l, "Consuming lemma function pointer chunk")) $. fun () ->
            let args = List.map (fun t -> TermPat t) (fterm::ftargs) in
            consume_chunk rules h ghostenv [] [] l (symb, true) fttargs real_unit dummypat (Some 1) args (fun _ h coef ts chunk_size ghostenv env env' ->
              if not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk permission required." None;
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
          let return_cont h tenv env retval =
            consume_chunk h (fun h -> return_cont h tenv env retval)
          in
          verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
    in
    match s with
      NonpureStmt (l, allowed, s) ->
      if allowed then
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes false leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
      else
        static_error l "Non-pure statements are not allowed here." None
    | ExprStmt (CallExpr (l, "produce_limits", [], [], [LitPat (Var (lv, x, _) as e)], Static)) ->
      if not pure then static_error l "This function may be called only from a pure context." None;
      if List.mem x ghostenv then static_error l "The argument for this call must be a non-ghost variable." None;
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      assume_is_of_type l (ev w) tp (fun () -> cont h env)
    | ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause_opt, body) ->
      verify_produce_function_pointer_chunk_stmt Ghost l e ftclause_opt body
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, args, params, openBraceLoc, ss, closeBraceLoc) ->
      verify_produce_function_pointer_chunk_stmt Real l fpe (Some (ftn, [], args, params, openBraceLoc, ss, closeBraceLoc)) None
    | ExprStmt (CallExpr (l, "close_struct", targs, [], args, Static)) when language = CLang ->
      let e = match (targs, args) with ([], [LitPat e]) -> e | _ -> static_error l "close_struct expects no type arguments and one argument." None in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of close_struct must be of type pointer-to-struct." None in
      let (_, fds_opt, padding_predsymb_opt) = List.assoc sn structmap in
      let fds = match fds_opt with Some fds -> fds | None -> static_error l "Cannot close a struct that does not declare a body." None in
      let padding_predsymb = match padding_predsymb_opt with Some s -> s | None -> static_error l "Cannot close a struct that declares ghost fields." None in
      eval_h h env e $. fun h env pointerTerm ->
      with_context (Executing (h, env, l, "Consuming character array")) $. fun () ->
      let (_, _, _, _, chars_symb, _) = List.assoc ("chars") predfammap in
      consume_chunk rules h ghostenv [] [] l (chars_symb, true) [] real_unit dummypat None [TermPat pointerTerm; SrcPat DummyPat] $. fun _ h coef ts _ _ _ _ ->
      if not (definitely_equal coef real_unit) then assert_false h env l "Closing a struct requires full permission to the character array." None;
      let [_; cs] = ts in
      with_context (Executing (h, env, l, "Checking character array length")) $. fun () ->
      let Some (_, _, _, _, length_symb) = try_assoc' (pn,ilist) "length" purefuncmap in
      if not (definitely_equal (mk_app length_symb [cs]) (List.assoc sn struct_sizes)) then
        assert_false h env l "Could not prove that length of character array equals size of struct." None;
      produce_c_object l real_unit pointerTerm (StructType sn) None false h $. fun h ->
      cont (Chunk ((padding_predsymb, true), [], real_unit, [pointerTerm], None)::h) env
    | ExprStmt (CallExpr (l, "open_struct", targs, [], args, Static)) when language = CLang ->
      let e = match (targs, args) with ([], [LitPat e]) -> e | _ -> static_error l "open_struct expects no type arguments and one argument." None in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of open_struct must be of type pointer-to-struct." None in
      let (_, fds_opt, padding_predsymb_opt) = List.assoc sn structmap in
      let fds = match fds_opt with Some fds -> fds | None -> static_error l "Cannot open a struct that does not declare a body." None in
      let padding_predsymb = match padding_predsymb_opt with Some s -> s | None -> static_error l "Cannot open a struct that declares ghost fields." None in
      eval_h h env e $. fun h env pointerTerm ->
      consume_c_object l pointerTerm (StructType sn) h $. fun h ->
      with_context (Executing (h, env, l, "Consuming struct padding chunk")) $. fun () ->
      consume_chunk rules h ghostenv [] [] l (padding_predsymb, true) [] real_unit dummypat None [TermPat pointerTerm] $. fun _ h coef _ _ _ _ _ ->
      if not (definitely_equal coef real_unit) then assert_false h env l "Opening a struct requires full permission to the struct padding chunk." None;
      let (_, _, _, _, chars_symb, _) = List.assoc "chars" predfammap in
      let cs = get_unique_var_symb "cs" (InductiveType ("list", [Char])) in
      let Some (_, _, _, _, length_symb) = try_assoc' (pn,ilist) "length" purefuncmap in
      assume (ctxt#mk_eq (mk_app length_symb [cs]) (List.assoc sn struct_sizes)) $. fun () ->
      cont (Chunk ((chars_symb, true), [], real_unit, [pointerTerm; cs], None)::h) env
    | ExprStmt (CallExpr (l, "free", [], [], args,Static) as e) ->
      let args = List.map (function LitPat e -> e | _ -> static_error l "No patterns allowed here" None ) args in
      begin
        match List.map (check_expr (pn,ilist) tparams tenv) args with
          [(arg, PtrType t)] when t <> Void && t <> Char ->
          if pure then static_error l "Cannot call a non-pure function from a pure context." None;
          let arg = ev arg in
          consume_c_object l arg t h $. fun h ->
          begin match t with
            StructType sn ->
            let (_, (_, _, _, _, malloc_block_symb, _)) = List.assoc sn malloc_block_pred_map in
            consume_chunk rules h [] [] [] l (malloc_block_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat arg] $. fun _ h _ _ _ _ _ _ ->
            cont h env
          | _ ->
            consume_chunk rules h [] [] [] l (get_pred_symb "malloc_block", true) [] real_unit real_unit_pat (Some 1) [TermPat arg; TermPat (sizeof l t)] $. fun _ h _ _ _ _ _ _ ->
            cont h env
          end
        | _ ->
          let (w, _) = check_expr (pn,ilist) tparams tenv e in
          verify_expr false h env None w (fun h env _ -> cont h env) econt
      end
    | ExprStmt (CallExpr (l, "set_verifast_verbosity", [], [], [LitPat (IntLit (_, n, _))], Static)) when pure ->
      let oldv = !verbosity in
      set_verbosity (int_of_big_int n);
      cont h env;
      set_verbosity oldv
    | ExprStmt (CallExpr (l, "init_class", [], [], args, Static)) when pure ->
      let cn =
        match args with
          [LitPat (ClassLit (l, cn))] ->
          let cn = check_classname (pn, ilist) (l, cn) in
          cn
        | [] ->
          let ClassOrInterfaceName cn = List.assoc current_class tenv in
          cn
        | _ -> static_error l "Syntax error. Syntax: 'init_class(MyClass.class);'." None
      in
      let (_, _, _, _, token_psymb, _) = List.assoc "java.lang.class_init_token" predfammap in
      let classterm = List.assoc cn classterms in
      consume_chunk rules h [] [] [] l (token_psymb, true) [] real_unit real_unit_pat (Some 1) [TermPat classterm] $. fun _ h _ _ _ _ _ _ ->
      let {cfds} = List.assoc cn classmap in
      let rec iter h1 fds =
        match fds with
          [] -> cont (h1 @ h) env
        | (fn, {ft;fbinding;finit;fvalue})::fds when fbinding = Static && !fvalue = Some None ->
          begin fun cont ->
            match finit with
              None -> cont h1 [] (default_value ft)
            | Some e -> eval_h h1 [] e cont
          end $. fun h1 [] v ->
          let (_, (_, _, _, _, symb, _)) = List.assoc (cn, fn) field_pred_map in
          produce_chunk h1 (symb, true) [] real_unit (Some 0) [v] None $. fun h1 ->
          iter h1 fds
        | _::fds ->
          iter h1 fds
      in
      iter [] cfds
    | ExprStmt (CallExpr (l, "open_module", [], [], args, Static)) ->
      if args <> [] then static_error l "open_module requires no arguments." None;
      let (_, _, _, _, module_symb, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
      consume_chunk rules h [] [] [] l (module_symb, true) [] real_unit (SrcPat DummyPat) (Some 2) [TermPat current_module_term; TermPat ctxt#mk_true] $. fun _ h coef _ _ _ _ _ ->
      begin fun cont ->
        let rec iter h globals =
          match globals with
            [] -> cont h
          | (x, (_, tp, addr, init))::globals ->
            produce_c_object l coef addr tp (Some !init) true h $. fun h ->
            iter h globals
        in
        iter h globalmap
      end $. fun h ->
      let codeChunks =
        if unloadable then [Chunk ((module_code_symb, true), [], coef, [current_module_term], None)] else []
      in
      cont (codeChunks @ h) env
    | ExprStmt (CallExpr (l, "close_module", [], [], args, Static)) ->
      if args <> [] then static_error l "close_module requires no arguments." None;
      let (_, _, _, _, module_symb, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
      begin fun cont ->
        let rec iter h globals =
          match globals with
            [] -> cont h
          | (x, (lg, tp, addr, init))::globals ->
            consume_c_object l addr tp h $. fun h ->
            iter h globals
        in
        iter h globalmap
      end $. fun h ->
      begin fun cont ->
        if unloadable then
          consume_chunk rules h [] [] [] l (module_code_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat current_module_term] $. fun _ h _ _ _ _ _ _ ->
          cont h
        else
          cont h
      end $. fun h ->
      cont (Chunk ((module_symb, true), [], real_unit, [current_module_term; ctxt#mk_false], None)::h) env
    | DeclStmt (ld, xs) ->
      let rec iter h tenv ghostenv env xs =
        match xs with
          [] -> tcont sizemap tenv ghostenv h env
        | (l, te, x, e, address_taken)::xs ->
          let t = check_pure_type (pn,ilist) tparams te in
          if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
          let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
          let produce_object envTp =
            if pure then static_error l "Cannot declare a variable of this type in a ghost context." None;
            let init =
              match e with
                None -> None
              | Some e -> Some (Some (check_c_initializer e t))
            in
            let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType Void) in
            produce_c_object l real_unit addr t init true h $. fun h ->
            iter h ((x, envTp)::tenv) ghostenv ((x, addr)::env) xs
          in
          match t with
            StaticArrayType (elemTp, elemCount) ->
            produce_object t
          | StructType sn ->
            produce_object (RefType t)
          | _ ->
            begin fun cont ->
              match e with
                None -> cont h env (get_unique_var_symb_non_ghost x t)
              | Some e ->
                let w = check_expr_t (pn,ilist) tparams tenv e t in
                verify_expr false h env (Some x) w (fun h env v -> cont h env v) econt
            end $. fun h env v ->
            if !address_taken then
              let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType t) in
              let h = ((Chunk ((pointee_pred_symb l t, true), [], real_unit, [addr; v], None)) :: h) in
              if pure then static_error l "Taking the address of a ghost variable is not allowed." None;
              iter h ((x, RefType(t)) :: tenv) ghostenv ((x, addr)::env) xs
            else
              iter h ((x, t) :: tenv) ghostenv ((x, v)::env) xs
      in
      iter h tenv ghostenv env xs
    | ExprStmt e ->
      let (w, _) = check_expr (pn,ilist) tparams tenv e in
      verify_expr false h env None w (fun h env _ -> cont h env) econt
    | IfStmt (l, e, ss1, ss2) ->
      if not pure then begin
        begin match ss1 with [PureStmt (lp, _)] -> static_error lp "Pure statement not allowed here." None | _ -> () end;
        begin match ss2 with [PureStmt (lp, _)] -> static_error lp "Pure statement not allowed here." None | _ -> () end;
      end;
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (eval_h_nonpure h env w ( fun h env w ->
        branch
          (fun _ -> assume w (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss1 tcont return_cont econt))
          (fun _ -> assume (ctxt#mk_not w) (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss2 tcont return_cont econt))
      ))
    | SwitchStmt (l, e, cs) ->
      let lblenv = ("#break", fun blocks_done sizemap tenv ghostenv h env -> cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env))::lblenv in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let verify_expr ro h env opt e cont = verify_expr ro h env opt e cont econt in 
      verify_expr false h env None w $. fun h env v ->
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      begin match tp with
        InductiveType (i, targs) ->
        let (tn, targs, Some (_, tparams, ctormap, _)) = (i, targs, try_assoc' (pn,ilist) i inductivemap) in
        let (Some tpenv) = zip tparams targs in
        let rec iter ctors cs =
          match cs with
            [] ->
            begin
            match ctors with
              [] -> success()
            | _ -> static_error l ("Missing clauses: " ^ String.concat ", " ctors) None
            end
          | SwitchStmtDefaultClause (l, _) :: cs -> static_error l "default clause not allowed in switch over inductive datatype" None
          | SwitchStmtClause (lc, e, ss)::cs ->
            let (cn, pats) =
              match e with
                CallExpr (lcall, cn, [], [], args, Static) ->
                let pats = List.map (function LitPat (Var (_, x, _)) -> x | _ -> static_error l "Constructor pattern arguments must be variable names" None) args in
                (cn, pats)
              | Var (_, cn, _) -> (cn, [])
              | _ -> static_error l "Case expression must be constructor pattern" None
            in
            let pts =
              match try_assoc' (pn,ilist) cn ctormap with
                None -> static_error lc ("Not a constructor of type " ^ tn) None
              | Some (_, (l, _, _, pts, _)) -> pts
            in
            let _ = if not (List.mem cn ctors) then static_error lc "Constructor already handled in earlier clause." None in
            let (ptenv, xterms, xenv) =
              let rec iter ptenv xterms xenv pats pts =
                match (pats, pts) with
                  ([], []) -> (List.rev ptenv, List.rev xterms, List.rev xenv)
                | (pat::pats, tp::pts) ->
                  if List.mem_assoc pat tenv then static_error lc ("Pattern variable '" ^ pat ^ "' hides existing local variable '" ^ pat ^ "'.") None;
                  if List.mem_assoc pat ptenv then static_error lc "Duplicate pattern variable." None;
                  let tp' = instantiate_type tpenv tp in
                  let term = get_unique_var_symb pat tp' in
                  let term' =
                    match unfold_inferred_type tp with
                      TypeParam x -> convert_provertype term (provertype_of_type tp') ProverInductive
                    | _ -> term
                  in
                  iter ((pat, tp')::ptenv) (term'::xterms) ((pat, term)::xenv) pats pts
                | ([], _) -> static_error lc "Too few arguments." None
                | _ -> static_error lc "Too many arguments." None
              in
              iter [] [] [] pats pts
            in
            let Some (_, _, _, _, ctorsym) = try_assoc' (pn,ilist) cn purefuncmap in
            let sizemap =
              match try_assq v sizemap with
                None -> sizemap
              | Some k -> List.map (fun (x, t) -> (t, k - 1)) xenv @ sizemap
            in
            branch
              (fun _ -> assume_eq v (mk_app ctorsym xterms) (fun _ -> verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap (ptenv @ tenv) (pats @ ghostenv) h (xenv @ env) ss tcont return_cont econt))
              (fun _ -> iter (List.filter (function cn' -> cn' <> cn) ctors) cs)
        in
        iter (List.map (function (cn, _) -> cn) ctormap) cs
      | Char | ShortType | IntType -> 
        let n = List.length (List.filter (function SwitchStmtDefaultClause (l, _) -> true | _ -> false) cs) in
        if n > 1 then static_error l "switch statement can have at most one default clause" None;
        let cs0 = cs in
        let rec fall_through h env cs =
          match cs with
            [] -> cont h env
          | c::cs ->
            let ss =
              match c with
                SwitchStmtDefaultClause (l, ss) -> ss
              | SwitchStmtClause (l, e, ss) -> ss
            in
            let tcont _ _ _ h env = fall_through h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) cs in
            verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt
        in
        let rec verify_cases cs =
          match cs with
            [] -> if n = 0 then (* implicit default *) cont h env
          | c::cs' ->
            begin match c with
              SwitchStmtClause (l, i, ss) ->
              let w2 = check_expr_t (pn,ilist) tparams tenv i IntType in
              eval_h h env w2 $. fun h env t ->
              assume_eq t v $. fun () ->
              fall_through h env cs
            | SwitchStmtDefaultClause (l, ss) ->
              let restr =
                List.fold_left
                  begin fun state clause -> 
                    match clause with
                      SwitchStmtClause (l, i, ss) -> 
                        let w2 = check_expr_t (pn,ilist) tparams tenv i IntType in
                        ctxt#mk_and state (ctxt#mk_not (ctxt#mk_eq v (ev w2))) 
                    | _ -> state
                  end
                  ctxt#mk_true cs0
              in
              assume restr $. fun () ->
              fall_through h env cs
            end;
            verify_cases cs'
        in
        verify_cases cs
      | _ -> static_error l "Switch statement operand is not an inductive value or integer." None
      end
    | Assert(_, ExprAsn(le, e)) -> 
      let we = check_expr_t (pn,ilist) tparams tenv e boolt in
      let t = eval env we in
      assert_term t h env le ("Assertion might not hold: " ^ (ctxt#pprint t)) None;
      cont h env
    | Assert (l, p) ->
      let (wp, tenv, _) = check_asn_core (pn,ilist) tparams tenv p in
      consume_asn rules [] h ghostenv env wp false real_unit (fun _ _ ghostenv env _ ->
        tcont sizemap tenv ghostenv h env
      )
    | Leak (l, p) ->
      let (wp, tenv, _) = check_asn_core (pn,ilist) tparams tenv p in
      consume_asn rules [] h ghostenv env wp false real_unit (fun chunks h ghostenv env size ->
        let coef = get_dummy_frac_term () in
        let chunks = List.map (fun (Chunk (g, targs, _, args, size)) -> Chunk (g, targs, coef, args, size)) chunks in
        tcont sizemap tenv ghostenv (chunks @ h) env
      )
    | Open (l, target, g, targs, pats0, pats, coefpat) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let open_instance_predicate target target_cn =
        let cn =
          match pats0 with
            [] -> target_cn
          | [LitPat (ClassLit (l, x))] ->
            begin match resolve (pn,ilist) l x classmap with
              None -> static_error l "Index: No such class" None
            | Some (cn, _) ->
              if is_subtype_of target_cn cn then
                cn
              else
                static_error l "Target object type must be subtype of index." None
            end
          | _ -> static_error l "Index should be of the form C.class." None
        in
        let (pmap, symb, body) =
          match try_assoc cn classmap with
            Some {cpreds} ->
            begin match try_assoc g cpreds with
              None -> static_error l "No such predicate instance" None
            | Some (lp, pmap, family, symb, body_opt) ->
              match body_opt with
                None -> static_error l "Predicate does not have a body" None
              | Some body -> (pmap, symb, body)
            end
          | None -> static_error l "Target of predicate instance call must be of class type" None
        in
        let index = List.assoc cn classterms in
        let env0 = [("this", target)] in
        ([], [], (symb, true), [TermPat target; TermPat index], 2, List.map (fun (x, t) -> (x, t, t)) pmap, env0, body, Some 2)
      in
      let (targs, tpenv, g_symb, pats0, dropcount, ps, env0, p, inputParamCount) =
        match target with
          Some target ->
          let (target, targetType) = check_expr (pn,ilist) tparams tenv target in
          let target_cn =
            match targetType with
              ObjType cn -> cn
            | _ -> static_error l "Target of predicate instance call must be of class type" None
          in
          let target = ev target in
          open_instance_predicate target target_cn
        | None ->
        let open_pred_inst0 g =
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x))-> (l,x) | _ -> static_error l "Predicate family indices must be class names." None) pats0)
          | _ -> List.map (function LitPat (Var (l, x, _)) -> x | _ -> static_error l "Predicate family indices must be function names." None) pats0
          in
          begin
            let index_term fn =
              match file_type path with
                Java-> List.assoc fn classterms
              | _ -> funcnameterm_of funcmap fn
            in
            match try_assoc (g, fns) predinstmap with
              Some (predenv, _, predinst_tparams, ps, g_symb, inputParamCount, p) ->
              let (targs, tpenv) =
                let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predinst_tparams else targs in
                match zip predinst_tparams targs with
                  None -> static_error l (Printf.sprintf "Predicate expects %d type arguments." (List.length predinst_tparams)) None
                | Some bs -> (targs, bs)
              in
              let ps = List.map (fun (x, t) -> (x, t, instantiate_type tpenv t)) ps in
              let inputParamCount = match inputParamCount with None -> None | Some n -> Some (List.length fns + n) in
              Some (targs, tpenv, (g_symb, true), List.map (fun fn -> TermPat (index_term fn)) fns, List.length fns, ps, predenv, p, inputParamCount)
            | None ->
              None
          end
        in
        let open_pred_inst g = 
          match resolve (pn,ilist) l g predfammap with
            Some (g, _) -> open_pred_inst0 g
          | None ->
          match try_assoc g tenv with
            Some (PredType _) -> open_pred_inst0 g
          | _ -> None
        in
        match open_pred_inst g with
          Some result -> result
        | None ->
          begin
          match try_assoc' (pn,ilist) g predctormap with
            None ->
            begin match try_assoc "this" tenv with
              None -> static_error l "No such predicate instance." None
            | Some (ObjType target_cn) ->
              let this = List.assoc "this" env in
              open_instance_predicate this target_cn
            end
          | Some (PredCtorInfo (_, ps1, ps2, body, funcsym)) ->
            if targs <> [] then static_error l "Predicate constructor expects 0 type arguments." None;
            let bs0 =
              match zip pats0 ps1 with
                None -> static_error l "Incorrect number of predicate constructor arguments." None
              | Some bs ->
                List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions." None) bs
            in
            let g_symb = mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
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
      let wpats = (List.map (function (LitPat e) -> (TermPat (eval_non_pure true h env e)) | wpat -> SrcPat wpat) wpats) in
      let pats = pats0 @ wpats in
      consume_chunk rules h ghostenv env [] l g_symb targs real_unit (SrcPat coefpat) inputParamCount pats (fun _ h coef ts chunk_size ghostenv env [] ->
        let ts = drop dropcount ts in
        let env' =
          List.map
            begin fun ((p, tp0, tp), t) ->
             (p, prover_convert_term t tp tp0)
            end
            (let Some bs = zip ps ts in bs)
        in
        let env' = env0 @ env' in
        let body_size = match chunk_size with Some (PredicateChunkSize k) -> Some (PredicateChunkSize (k - 1)) | _ -> None in
        with_context PushSubcontext (fun () ->
          produce_asn tpenv h ghostenv env' p coef body_size body_size (fun h _ _ ->
            with_context PopSubcontext (fun () -> tcont sizemap tenv' ghostenv h env)
          )
        )
      )
    | SplitFractionStmt (l, p, targs, pats, coefopt) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, g_symb, pts, inputParamCount) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate." None
        | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount) ->
          let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predfam_tparams else targs in
          let tpenv =
            match zip predfam_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          if arity <> 0 then static_error l "Predicate families are not supported in split_fraction statements." None;
          (targs, (g_symb, true), instantiate_types tpenv pts, inputParamCount)
      in
      let splitcoef =
        match coefopt with
          None -> real_half
        | Some e ->
          let w = check_expr_t (pn,ilist) tparams tenv e RealType in
          let coef = ev w in
          assert_term (ctxt#mk_real_lt real_zero coef) h env l "Split coefficient must be positive." None;
          assert_term (ctxt#mk_real_lt coef real_unit) h env l "Split coefficient must be less than one." None;
          coef
      in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      consume_chunk rules h ghostenv env [] l g_symb targs real_unit dummypat inputParamCount (srcpats wpats) (fun _ h coef ts chunk_size ghostenv env [] ->
        let coef1 = ctxt#mk_real_mul splitcoef coef in
        let coef2 = ctxt#mk_real_mul (ctxt#mk_real_sub real_unit splitcoef) coef in
        let h = Chunk (g_symb, targs, coef1, ts, None)::Chunk (g_symb, targs, coef2, ts, None)::h in
        tcont sizemap tenv' ghostenv h env
      )
    | MergeFractionsStmt (l, p, targs, pats) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, g_symb, pts, inputParamCount) =
        match try_assoc' (pn,ilist) p predfammap with
          None -> static_error l "No such predicate." None
        | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount) ->
          let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predfam_tparams else targs in
          let tpenv =
            match zip predfam_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          if arity <> 0 then static_error l "Predicate families are not supported in merge_fractions statements." None;
          begin
            match inputParamCount with
              None ->
              static_error l
                ("Cannot merge this predicate: it is not declared precise. "
                 ^ "To declare a predicate precise, separate the input parameters "
                 ^ "from the output parameters using a semicolon in the predicate declaration.") None;
            | Some n -> (targs, (g_symb, true), instantiate_types tpenv pts, n)
          end
      in
      let (pats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      let (inpats, outpats) = take_drop inputParamCount pats in
      List.iter (function (LitPat e) -> () | _ -> static_error l "No patterns allowed at input positions." None) inpats;
      let pats = srcpats pats in
      consume_chunk rules h ghostenv env [] l g_symb targs real_unit dummypat (Some inputParamCount) pats (fun _ h coef1 ts1 _ ghostenv env [] ->
        consume_chunk rules h ghostenv env [] l g_symb targs real_unit dummypat (Some inputParamCount) pats (fun _ h coef2 ts2 _ _ _ [] ->
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
          None -> static_error l "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let Some (_, _, _, pts, g_symb, _) = try_assoc' (pn,ilist) bcn predfammap in
      let (pats, tenv) = check_pats (pn,ilist) l tparams tenv pts pats in
      consume_chunk rules h ghostenv env [] l (g_symb, true) [] real_unit dummypat None (srcpats pats) $. fun _ h coef ts _ ghostenv env [] ->
      if not (definitely_equal coef real_unit) then static_error l "Disposing a box requires full permission." None;
      let boxId::argts = ts in
      let Some boxArgMap = zip boxpmap argts in
      let boxArgMap = List.map (fun ((x, _), t) -> (x, t)) boxArgMap in
      with_context PushSubcontext $. fun () ->
      produce_asn [] h ghostenv boxArgMap inv real_unit None None $. fun h _ boxVarMap ->
      let rec dispose_handles tenv ghostenv h env handleClauses cont =
        match handleClauses with
          [] -> cont tenv ghostenv h env
        | (l, hpn, pats)::handleClauses ->
          begin
            match try_assoc hpn hpmap with
              None -> static_error l "No such handle predicate." None
            | Some (lhp, hpParamMap, hpInv, pbcs) ->
              let hpParamTypes = List.map (fun (x, t) -> t) hpParamMap in
              let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv (HandleIdType::hpParamTypes) pats in
              let wpats = srcpats wpats in
              let Some (_, _, _, _, hpn_symb, _) = try_assoc' (pn,ilist) hpn predfammap in
              let handlePat::argPats = wpats in
              let pats = handlePat::TermPat boxId::argPats in
              consume_chunk rules h ghostenv env [] l (hpn_symb, true) [] real_unit dummypat None pats $. fun _ h coef ts _ ghostenv env [] ->
              if not (definitely_equal coef real_unit) then static_error l "Disposing a handle predicate requires full permission." None;
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
    | Close (l, target, g, targs, pats0, pats, coef) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let close_instance_predicate target target_cn =
        let cn =
          match pats0 with
            [] -> target_cn
          | [LitPat (ClassLit (l, x))] ->
            begin match resolve (pn,ilist) l x classmap with
              None -> static_error l "Index: No such class" None
            | Some (cn, _) ->
              if is_subtype_of target_cn cn then
                cn
              else
                static_error l "Target object type must be subtype of index." None
            end
          | _ -> static_error l "Index should be of the form C.class." None
        in
        let (lpred, pmap, symb, body) =
          match try_assoc cn classmap with
            Some {cpreds} ->
            begin match try_assoc g cpreds with
              None -> static_error l "No such predicate instance" None
            | Some (lp, pmap, family, symb, body_opt) ->
              match body_opt with
                None -> static_error l "Predicate does not have a body" None
              | Some body -> (lp, pmap, symb, body)
            end
          | None -> static_error l "Target of predicate instance call must be of class type" None
        in
        let index = List.assoc cn classterms in
        (lpred, [], [], pmap, [("this", target)], (symb, true), body, [target; index], Some 1)
      in
      let (lpred, targs, tpenv, ps, bs0, g_symb, p, ts0, inputParamCount) =
        match target with
          Some target ->
          let (target, targetType) = check_expr (pn,ilist) tparams tenv target in
          let target_cn =
            match targetType with
              ObjType cn -> cn
            | _ -> static_error l "Target of predicate instance call must be of class type" None
          in
          let target = ev target in
          close_instance_predicate target target_cn
        | None ->
        let close_pred_inst0 g =
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x)) -> (l, x) | _ -> static_error l "Predicate family indices must be class names." None) pats0)
          | _ -> List.map (function LitPat (Var (l, x, _)) -> x | _ -> static_error l "Predicate family indices must be function names." None) pats0
          in
          begin
          match try_assoc (g, fns) predinstmap with
            Some (predenv, lpred, predinst_tparams, ps, g_symb, inputParamCount, body) ->
            let targs = if targs = [] then List.map (fun _ -> InferredType (ref None)) predinst_tparams else targs in
            let tpenv =
              match zip predinst_tparams targs with
                None -> static_error l "Incorrect number of type arguments." None
              | Some bs -> bs
            in
            let ts0 = match file_type path with
              Java -> List.map (fun cn -> List.assoc cn classterms) fns
            | _ -> List.map (fun fn -> funcnameterm_of funcmap fn) fns
            in
            Some (lpred, targs, tpenv, ps, predenv, (g_symb, true), body, ts0, inputParamCount)
          | None -> None
          end
        in
        let close_pred_inst g =
          match resolve (pn,ilist) l g predfammap with
            Some (g, _) -> close_pred_inst0 g
          | None ->
          match try_assoc g tenv with
            Some (PredType _) -> close_pred_inst0 g
          | _ -> None
        in
        match close_pred_inst g with
          Some result -> result
        | None ->
          begin
            match try_assoc' (pn,ilist) g predctormap with
              None ->
              begin match try_assoc "this" tenv with
                Some (ObjType cn) ->
                let this = List.assoc "this" env in
                close_instance_predicate this cn
              | _ -> static_error l "No such predicate instance." None
              end
            | Some (PredCtorInfo (lpred, ps1, ps2, body, funcsym)) ->
              let bs0 =
                match zip pats0 ps1 with
                  None -> static_error l "Incorrect number of predicate constructor arguments." None
                | Some bs ->
                  List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions." None) bs
              in
              let g_symb = mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
              if targs <> [] then static_error l "Incorrect number of type arguments." None;
              (lpred, [], [], ps2, bs0, (g_symb, false), body, [], None)
          end
      in
      let ps =
        match zip pats ps with
          None -> static_error l "Wrong number of arguments." None
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
        | _ -> static_error l "Coefficient in close statement must be expression." None
      in
      let env' = flatmap (function (p, pat, tp0, tp, Some t) -> [(p, prover_convert_term t tp tp0)] | _ -> []) ps in
      let env' = bs0 @ env' in
      with_context PushSubcontext (fun () ->
        consume_asn rules tpenv h ghostenv env' p true coef (fun _ h p_ghostenv p_env size_first ->
          with_context (Executing (h, p_env, lpred, "Inferring chunk arguments")) $. fun () ->
          let ts =
            List.map
              begin fun (p, pat, tp0, tp, t) ->
                match t with
                  Some t -> ([], t)
                | None ->
                  let t =
                    match try_assoc p p_env with
                      None -> assert_false h p_env l (Printf.sprintf "Predicate body does not bind parameter '%s'; it must be supplied in the close statement." p) None
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
          produce_chunk h g_symb targs coef inputParamCount (ts0 @ ts) None $. fun h ->
          cont h env
        )
      )
    | CreateBoxStmt (l, x, bcn, args, handleClauses) ->
      if not pure then static_error l "Box creation statements are allowed only in a pure context." None;
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' (pn,ilist) bcn boxmap with
          None -> static_error l "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let (tenv, ghostenv, env) =
        let rec iter tenv ghostenv env handleClauses =
          match handleClauses with
            [] -> (tenv, ghostenv, env)
          | (l, x, hpn, args)::handleClauses ->
            if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
            iter ((x, HandleIdType)::tenv) (x::ghostenv) ((x, get_unique_var_symb x HandleIdType)::env) handleClauses
        in
        iter tenv ghostenv env handleClauses
      in
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
      let boxArgMap =
        match zip args boxpmap with
          None -> static_error l "Incorrect number of arguments." None
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
      consume_asn rules [] h ghostenv boxArgMap inv true real_unit $. fun _ h _ boxVarMap _ ->
      let boxIdTerm = get_unique_var_symb x BoxIdType in
      begin fun cont ->
        let rec iter handleChunks handleClauses =
          match handleClauses with
            (l, x, hpn, args)::handleClauses ->
            begin
            match try_assoc hpn hpmap with
              None -> static_error l "No such handle predicate" None
            | Some (lhp, hpParamMap, hpInv, pbcs) ->
              let hpArgMap =
                match zip hpParamMap args with
                  None -> static_error l "Incorrect number of arguments." None
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
              assert_term (eval hpInvEnv hpInv) h hpInvEnv (expr_loc hpInv) "Cannot prove handle predicate invariant." None;
              let (_, _, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with 
                None-> static_error l ("No such predicate family: "^hpn) None
              | Some x -> x
              in
              iter (Chunk ((hpn_symb, true), [], real_unit, handleIdTerm::boxIdTerm::List.map (fun (x, t) -> t) hpArgMap, None)::handleChunks) handleClauses
            end
          | [] -> cont handleChunks
        in
        iter [] handleClauses
      end $. fun handleChunks ->
      let (_, _, _, _, bcn_symb, _) = match try_assoc' (pn,ilist) bcn predfammap with
        None -> static_error l ("No such predicate family: "^bcn) None
      | Some x-> x
      in
      with_context PopSubcontext $. fun () ->
      tcont sizemap ((x, BoxIdType)::tenv) (x::ghostenv) (Chunk ((bcn_symb, true), [], real_unit, boxIdTerm::boxArgs, None)::(handleChunks@h)) ((x, boxIdTerm)::env)
    | CreateHandleStmt (l, x, hpn, arg) ->
      if not pure then static_error l "Handle creation statements are allowed only in a pure context." None;
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
      let bcn =
        match chop_suffix hpn "_handle" with
          None -> static_error l "Handle creation statement must mention predicate name that ends in '_handle'." None
        | Some bcn -> match try_assoc' (pn,ilist) bcn boxmap with
            None-> static_error l "No such box class." None
          | Some bcn -> bcn
      in
      let w = check_expr_t (pn,ilist) tparams tenv arg BoxIdType in
      let boxIdTerm = ev w in
      let handleTerm = get_unique_var_symb x HandleIdType in
      let (_, _, _, _, hpn_symb, _) = match try_assoc' (pn,ilist) hpn predfammap with
        None -> static_error l ("No such predicate family: "^hpn) None
      | Some x-> x
      in
      tcont sizemap ((x, HandleIdType)::tenv) (x::ghostenv) (Chunk ((hpn_symb, true), [], real_unit, [handleTerm; boxIdTerm], None)::h) ((x, handleTerm)::env)
    | ReturnStmt (l, eo) ->
      verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env true l eo [] return_cont econt
    | WhileStmt (l, e, None, dec, ss) ->
      static_error l "Loop invariant required." None
    | WhileStmt (l, e, Some (LoopInv p), dec, ss) ->
      if not pure then begin
        match ss with PureStmt (lp, _)::_ -> static_error lp "Pure statement not allowed here." None | _ -> ()
      end;
      if pure && (match dec with None -> true | _ -> false) then static_error l "Loops without a measure are not supported in a pure context." None;
      let endBodyLoc = match ss with BlockStmt(_, _, _, closeBraceLoc, _) :: _ -> closeBraceLoc | _-> l in
      let break h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let lblenv = ("#break", fun blocks_done sizemap tenv ghostenv h env -> break h env)::lblenv in
      let e = check_expr_t (pn,ilist) tparams tenv e boolt in
      if not pure then check_ghost ghostenv l e;
      let xs = (expr_assigned_variables e) @ (block_assigned_variables ss) in
      let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
      let (p, tenv') = check_asn (pn,ilist) tparams tenv p in
      let dec = (match dec with None -> None | Some(e) -> Some(check_expr_t (pn,ilist) tparams tenv' e intt)) in
      consume_asn rules [] h ghostenv env p true real_unit $. fun _ h _ _ _ ->
      let lblenv =
        List.map
          begin fun (lbl, cont) ->
            (lbl, fun blocks_done sizemap tenv ghostenv h'' env -> cont blocks_done sizemap tenv ghostenv (h'' @ h) env)
          end
          lblenv
      in
      let return_cont h'' tenv env retval = return_cont (h'' @ h) tenv env retval in
      let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let env = bs @ env in
      produce_asn [] [] ghostenv env p real_unit None None $. fun h' ghostenv' env' ->
      begin fun cont ->
        match dec with
          None -> cont None
        | Some dec ->
          eval_h h' env' dec $. fun _ _ t_dec ->
          cont (Some t_dec)
      end $. fun t_dec ->
      eval_h_nonpure h' env' e $. fun h' env' v ->
      begin fun cont ->
        branch
          begin fun () ->
            assume v cont
          end
          begin fun () ->
            assume (ctxt#mk_not v) $. fun () ->
            tcont sizemap tenv' ghostenv' (h' @ h) env'
          end
      end $. fun () ->
      begin fun continue ->
        verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv' ghostenv' h' env' ss
          (fun _ _ _ h'' env -> continue h'' env)
          return_cont
          econt
      end $. fun h' env ->
      let env = List.filter (fun (x, _) -> List.mem_assoc x tenv) env in
      consume_asn rules [] h' ghostenv env p true real_unit $. fun _ h''' _ env''' _ ->
      check_leaks h''' env endBodyLoc "Loop leaks heap chunks.";
      begin match (t_dec, dec) with
        (None, None) -> ()
      | (Some t_dec, Some dec) ->
        eval_h h' env''' dec $. fun _ _ t_dec2 ->
        let dec_check1 = ctxt#mk_lt t_dec2 t_dec in
        assert_term dec_check1 h' env''' (expr_loc dec) (sprintf "Cannot prove that loop measure decreases: %s" (ctxt#pprint dec_check1)) None;
        let dec_check2 = ctxt#mk_le (ctxt#mk_intlit 0) t_dec in
        assert_term dec_check2 h' env''' (expr_loc dec) (sprintf "Cannot prove that the loop measure remains non-negative: %s" (ctxt#pprint dec_check2)) None
      end
    | WhileStmt (l, e, Some (LoopSpec (pre, post)), dec, ss) ->
      if not pure then begin
        match ss with PureStmt (lp, _)::_ -> static_error lp "Pure statement not allowed here." None | _ -> ()
      end;
      if pure && (match dec with None -> true | _ -> false) then static_error l "Loops without a measure are not supported in a pure context." None;
      let endBodyLoc = match ss with BlockStmt(_, _, _, closeBraceLoc, _) :: _ -> closeBraceLoc | _-> l in
      let break h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let lblenv = ("#break", fun blocks_done sizemap tenv ghostenv h env -> break h env)::lblenv in
      let e = check_expr_t (pn,ilist) tparams tenv e boolt in
      if not pure then check_ghost ghostenv l e;
      let (ss, locals_to_free) = (* do we really need to do this? Aren't locals freed automatically at the end of the loop if the body is a block? *)
        match ss with
          BlockStmt(_, _, ss, _, locals_to_free) :: rest -> check_block_declarations ss; (ss @ rest, locals_to_free)
        | _ -> (ss, ref [])
      in
      let xs = (expr_assigned_variables e) @ (block_assigned_variables ss) in
      let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
      let (pre, tenv') = check_asn (pn,ilist) tparams tenv pre in
      let old_xs_tenv = List.map (fun x -> ("old_" ^ x, List.assoc x tenv)) xs in
      let tenv'' = old_xs_tenv @ tenv' in
      let (post, tenv''') = check_asn (pn,ilist) tparams tenv'' post in
      let dec = match dec with None -> None | Some e -> Some (check_expr_t (pn,ilist) tparams tenv' e intt) in
      let ghostenv' = ghostenv in
      let env' = env in
      consume_asn rules [] h ghostenv env pre true real_unit $. fun _ h ghostenv env _ ->
      let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let old_xs_env = List.map (fun (x, t) -> ("old_" ^ x, t)) bs in
      let env' = bs @ env' in
      produce_asn [] [] ghostenv' env' pre real_unit None None $. fun h' ghostenv' env' ->
      begin fun cont ->
        match dec with
          None -> cont None
        | Some dec ->
          eval_h h' env' dec $. fun _ _ t_dec ->
          cont (Some t_dec)
      end $. fun t_dec ->
      let env' = old_xs_env @ env' in
      let ghostenv' = List.map (fun (x, _) -> x) old_xs_env @ ghostenv' in
      let check_post h' env' =
        consume_asn rules [] h' ghostenv' env' post true real_unit $. fun _ h' _ _ _ ->
        check_leaks h' env' endBodyLoc "Loop leaks heap chunks"
      in
      let exit_loop h' env' cont =
        check_post h' env';
        let env =
          flatmap
            begin fun (x, t) ->
              if List.mem x xs then
                [(x, List.assoc x env'); ("old_" ^ x, t)]
              else
                [(x, t)]
            end
            env
        in
        let ghostenv = List.map (fun (x, _) -> x) old_xs_tenv @ ghostenv in
        produce_asn [] h ghostenv env post real_unit None None $. fun h ghostenv env ->
        cont tenv''' ghostenv h env
      in
      let lblenv = List.map (fun (lbl, cont) -> (lbl, fun blocks_done sizemap ttenv _ h' env' -> free_locals endBodyLoc h' ttenv env' !locals_to_free (fun h' _ -> exit_loop h' env' (cont blocks_done sizemap)))) lblenv in
      let return_cont h' tenv env retval = assert_false h' [] l "Returning out of a requires-ensures loop is not yet supported." None in
      eval_h_nonpure h' env' e $. fun h' env' v ->
      begin fun cont ->
        branch
          begin fun () ->
            assume v cont
          end
          begin fun () ->
            assume (ctxt#mk_not v) $. fun () -> exit_loop h' env' (tcont sizemap)
          end
      end $. fun () ->
      let (ss_before, ss_after) =
        let rec iter ss_before ss =
          match ss with
            [] -> (List.rev ss_before, [])
          | PureStmt (_, ExprStmt (CallExpr (lc, "recursive_call", [], [], [], Static)))::ss_after -> (List.rev ss_before, ss_after)
          | s::ss_after -> iter (s::ss_before) ss_after
        in
        iter [] ss
      in
      begin fun continue ->
        verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv'' ghostenv' h' env' ss_before
          (fun _ tenv''' _ h' env' -> free_locals endBodyLoc h' tenv''' env' !locals_to_free (fun h' _ -> continue h' tenv''' env'))
          return_cont
          econt
      end $. fun h' tenv''' env' ->
      let env'' = List.filter (fun (x, _) -> List.mem_assoc x tenv) env' in
      consume_asn rules [] h' ghostenv env'' pre true real_unit $. fun _ h' ghostenv'' env'' _ ->
      begin match (t_dec, dec) with
        (None, None) -> ()
      | (Some t_dec, Some dec) ->
        eval_h h' env'' dec $. fun _ _ t_dec2 ->
        let dec_check1 = ctxt#mk_lt t_dec2 t_dec in
        assert_term dec_check1 h' env'' (expr_loc dec) (sprintf "Cannot prove that loop measure decreases: %s" (ctxt#pprint dec_check1)) None;
        let dec_check2 = ctxt#mk_le (ctxt#mk_intlit 0) t_dec in
        assert_term dec_check2 h' env'' (expr_loc dec) (sprintf "Cannot prove that the loop measure remains non-negative: %s" (ctxt#pprint dec_check2)) None
      end;
      let bs' = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let env'' =
        flatmap
          begin fun (x, t) ->
            if List.mem x xs then
              [("old_" ^ x, t); (x, List.assoc x bs')]
            else
              [(x, t)]
          end
          env''
      in
      produce_asn [] h' ghostenv'' env'' post real_unit None None $. fun h' _ _ ->
      let env' = bs' @ env' in
      List.iter (function PureStmt _ -> () | s -> static_error (stmt_loc s) "Only pure statements are allowed after the recursive call." None) ss_after;
      let ss_after_xs = block_assigned_variables ss_after in
      List.iter (fun x -> if List.mem x xs then static_error l "Statements after the recursive call are not allowed to assign to loop variables" None) ss_after_xs;
      verify_cont (pn,ilist) blocks_done [] tparams boxes pure leminfo funcmap predinstmap sizemap tenv''' ghostenv' h' env' ss_after (fun _ tenv _ h' env' ->  check_post h' env') (fun _ _ -> assert false) (fun _ _ _ -> assert false)
    | Throw (l, e) ->
      if pure then static_error l "Throw statements are not allowed in a pure context." None;
      let e' = check_expr_t (pn,ilist) tparams tenv e (ObjType "java.lang.Throwable") in
      check_ghost ghostenv l e';
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      if (is_unchecked_exception_type tp) then
        ()
      else
        verify_expr false h env None w (fun h env v -> (econt l h env tp v)) econt
    | TryCatch (l, body, catches) ->
      if pure then static_error l "Try-catch statements are not allowed in a pure context." None;
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      branch
        begin fun () ->
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont (fun throwl h env2 texcep excep -> 
            let env = List.filter (fun (x, t) -> List.mem_assoc x env) env2 in
            let rec iter catches =
              match catches with
                [] -> econt throwl h env texcep excep
              | (l, te, x, body)::catches ->
                let t = check_pure_type (pn,ilist) tparams te in
                branch
                  begin fun () ->
                    if((is_subtype_of_ texcep t) || (is_subtype_of_ t texcep)) then begin
                      if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
                      let tenv = (x, t)::tenv in
                      let env = (x, excep)::env in
                      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
                    end
                  end
                  begin fun () ->
                    begin if not (is_subtype_of_ texcep t) then
                      iter catches
                    end
                  end
              in
              iter catches
          )
        end
        begin fun () ->
          (* Havoc the variables that are assigned by the try block. *)
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
          let env = bs @ env in
          let h = [] in
          let rec iter catches =
            match catches with
              [] -> ()
            | (l, te, x, body)::catches ->
              branch
                begin fun () ->
                  if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
                  let t = check_pure_type (pn,ilist) tparams te in
                  if (is_unchecked_exception_type t) || t = (ObjType "java.lang.Exception") || t = (ObjType "java.lang.Throwable") then begin
                    let xterm = get_unique_var_symb_non_ghost x t in
                    let tenv = (x, t)::tenv in
                    let env = (x, xterm)::env in
                    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
                  end
                end
                begin fun () ->
                  iter catches
                end
          in
          iter catches
        end
    | TryFinally (l, body, lf, finally) ->
      if pure then static_error l "Try-finally statements are not allowed in a pure context." None;
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (* Tricky stuff; I hope this is correct... *)
      branch
        begin fun () ->
          let lblenv =
            List.map
              begin fun (lbl, cont) ->
                let cont blocks_done sizemap tenv ghostenv h env =
                  let tcont _ _ _ h env = cont blocks_done sizemap tenv ghostenv h env in
                  verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
                in
                (lbl, cont)
              end
              lblenv
          in
          let tcont _ _ _ h env =
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
          in
          let return_cont h tenv env retval =
            let tcont _ _ _ h _ = return_cont h tenv env retval in
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
          in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
        end
        begin fun () ->
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
          let env = bs @ env in
          let h = [] in
          let tcont _ _ _ _ _ = () in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
        end
    | PerformActionStmt (lcb, nonpure_ctxt, pre_bcn, pre_bcp_pats, lch, pre_hpn, pre_hp_pats, lpa, an, aargs, ss, closeBraceLoc, post_bcp_args_opt, lph, post_hpn, post_hp_args) ->
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' (pn,ilist) pre_bcn boxmap with
          None -> static_error lcb "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let pre_bcn=
        match search' pre_bcn (pn,ilist) boxmap with
          None-> static_error lcb "You cannot perform an action on a box class that has not yet been declared." None
        | Some pre_bcn -> pre_bcn
      in
      if not (List.mem pre_bcn boxes) then static_error lcb "You cannot perform an action on a box class that has not yet been declared." None;
      let (pre_bcp_pats, tenv) = check_pats (pn,ilist) lcb tparams tenv (BoxIdType::List.map (fun (x, t) -> t) boxpmap) pre_bcp_pats in
      let pre_bcp_pats = srcpats pre_bcp_pats in
      let (_, _, _, _, boxpred_symb, _) = match try_assoc' (pn,ilist) pre_bcn predfammap with 
        Some x->x
      | None -> static_error lcb ("Box predicate not found: "^pre_bcn) None
      in
      consume_chunk rules h ghostenv env [] lcb (boxpred_symb, true) [] real_unit dummypat None pre_bcp_pats (fun _ h box_coef ts chunk_size ghostenv env [] ->
        if box_coef != real_unit then assert_false h env lcb "Box predicate coefficient must be 1." None;
        let (boxId::pre_boxPredArgs) = ts in
        let (pre_handlePred_parammap, pre_handlePred_inv) =
          if pre_hpn = pre_bcn ^ "_handle" then
            ([], True lch)
          else
            match try_assoc' (pn,ilist) pre_hpn hpmap with
              None -> static_error lch "No such handle predicate in box class." None
            | Some (_, hppmap, inv, _) ->
              (hppmap, inv)
        in
        let (_, _, _, _, pre_handlepred_symb, _) = match try_assoc' (pn,ilist) pre_hpn predfammap with 
          Some x->x
        | None -> static_error lcb ("Box predicate not found: "^pre_bcn) None
        in
        let (pre_hp_pats, tenv) = check_pats (pn,ilist) lch tparams tenv (HandleIdType::List.map (fun (x, t) -> t) pre_handlePred_parammap) pre_hp_pats in
        let (pre_handleId_pat::pre_hpargs_pats) = srcpats pre_hp_pats in
        consume_chunk rules h ghostenv (("#boxId", boxId)::env) [] lch (pre_handlepred_symb, true) [] real_unit dummypat None (pre_handleId_pat::TermPat boxId::pre_hpargs_pats)
          (fun _ h coef ts chunk_size ghostenv env [] ->
             if not (coef == real_unit) then assert_false h env lch "Handle predicate coefficient must be 1." None;
             let (handleId::_::pre_handlePredArgs) = ts in
             let (apmap, pre, post) =
               match try_assoc an amap with
                 None -> static_error l "No such action in box class." None
               | Some (_, apmap, pre, post) -> (apmap, pre, post)
             in
             let aargbs =
               match zip apmap aargs with
                 None -> static_error lpa "Incorrect number of action arguments." None
               | Some bs ->
                 List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
             in
             let Some pre_boxargbs = zip boxpmap pre_boxPredArgs in
             let pre_boxArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_boxargbs in
             let Some pre_hpargbs = zip pre_handlePred_parammap pre_handlePredArgs in
             let pre_hpArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_hpargbs in
             with_context PushSubcontext $. fun () ->
             produce_asn [] h ghostenv pre_boxArgMap inv real_unit None None $. fun h _ pre_boxVarMap ->
             with_context PopSubcontext $. fun () ->
             assume (eval ([("predicateHandle", handleId)] @ pre_hpArgMap @ pre_boxVarMap) pre_handlePred_inv) (fun () ->
               let nonpureStmtCount = ref 0 in
               let ss =
                 List.map
                   begin function
                     NonpureStmt (l, _, s) when !nonpure_ctxt ->
                     nonpureStmtCount := !nonpureStmtCount + 1;
                     NonpureStmt (l, true, s)
                   | s -> s
                   end
                   ss
               in
               verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env ->
                 with_context (Executing (h, env, closeBraceLoc, "Closing box")) $. fun () ->
                 with_context PushSubcontext $. fun () ->
                 let pre_env = [("actionHandle", handleId)] @ pre_boxVarMap @ aargbs in
                 assert_term (eval pre_env pre) h pre_env closeBraceLoc "Action precondition failure." None;
                 let post_boxArgMap =
                   match post_bcp_args_opt with
                     None -> pre_boxArgMap
                   | Some (lpb, post_bcp_args) ->
                     begin
                       match zip boxpmap post_bcp_args with
                         None -> static_error lpb "Incorrect number of post-state box arguments." None
                       | Some bs ->
                         List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                     end
                 in
                 consume_asn rules [] h ghostenv post_boxArgMap inv true real_unit $. fun _ h _ post_boxVarMap _ ->
                 let old_boxVarMap = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxVarMap in
                 let post_env = [("actionHandle", handleId)] @ old_boxVarMap @ post_boxVarMap @ aargbs in
                 assert_term (eval post_env post) h post_env closeBraceLoc "Action postcondition failure." None;
                 let (post_handlePred_parammap, post_handlePred_inv) =
                   if post_hpn = pre_bcn ^ "_handle" then
                     ([], True l)
                   else
                     match try_assoc post_hpn hpmap with
                       None -> static_error lph "Post-state handle predicate: No such handle predicate in box class." None
                     | Some (_, hppmap, inv, _) ->
                       (hppmap, inv)
                 in
                 let (_, _, _, _, post_handlePred_symb, _) = match try_assoc' (pn,ilist) post_hpn predfammap with 
                   None-> static_error lph ("No such predicate family: "^post_hpn) None
                 | Some x-> x
                 in
                 let post_hpargs =
                   match zip post_handlePred_parammap post_hp_args with
                     None -> static_error lph "Post-state handle predicate: Incorrect number of arguments." None
                   | Some bs ->
                     List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                 in
                 let post_hpinv_env = [("predicateHandle", handleId)] @ post_hpargs @ post_boxVarMap in
                 with_context (Executing (h, post_hpinv_env, expr_loc post_handlePred_inv, "Checking post-state handle predicate invariant")) $. fun () ->
                 assert_term (eval post_hpinv_env post_handlePred_inv) h post_hpinv_env lph "Post-state handle predicate invariant failure." None;
                 let boxChunk = Chunk ((boxpred_symb, true), [], box_coef, boxId::List.map (fun (x, t) -> t) post_boxArgMap, None) in
                 let hpChunk = Chunk ((post_handlePred_symb, true), [], real_unit, handleId::boxId::List.map (fun (x, t) -> t) post_hpargs, None) in
                 let h = boxChunk::hpChunk::h in
                 with_context PopSubcontext $. fun () ->
                 tcont sizemap tenv ghostenv h env
               ) return_cont econt
             )
          )
      )
    | BlockStmt (l, ds, ss, closeBraceLoc, locals_to_free) ->
      let (lems, predinsts, localpreds, localpredinsts) =
        List.fold_left
          begin fun (lems, predinsts, localpreds, localpredinsts) decl ->
            match decl with
            | PredFamilyDecl (l, p, tparams, arity, tes, inputParamCount) ->
              if tparams <> [] then static_error l "Local predicates with type parameters are not yet supported." None;
              if arity <> 0 then static_error l "Local predicate families are not yet supported." None;
              if List.mem_assoc p predfammap then static_error l "Duplicate predicate family name." None;
              if List.mem_assoc p tenv then static_error l "Predicate name conflicts with local variable name." None;
              let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
              let ptype = PredType ([], ts, inputParamCount) in
              let psymb = get_unique_var_symb p ptype in
              (lems, predinsts, (p, (l, ts, inputParamCount, ptype, psymb))::localpreds, localpredinsts)
            | PredFamilyInstanceDecl (l, p, predinst_tparams, is, xs, body) ->
              begin match try_assoc p localpreds with
              | Some (_, ts, inputParamCount, ptype, psymb) ->
                if predinst_tparams <> [] then static_error l "Local predicates with type parameters are not yet supported." None;
                if is <> [] then static_error l "Local predicate families are not yet supported." None;
                if List.mem_assoc p localpredinsts then static_error l "Duplicate predicate family instance." None;
                (lems, predinsts, localpreds, (p, (l, ts, inputParamCount, ptype, psymb, xs, body))::localpredinsts)
              | None ->
                let i = match is with [i] -> i | _ -> static_error l "Local predicate family declarations must declare exactly one index." None in
                if List.mem_assoc (p, i) predinsts then static_error l "Duplicate predicate family instance." None;
                (lems, ((p, i), (l, predinst_tparams, xs, body))::predinsts, localpreds, localpredinsts)
              end
            | Func (l, Lemma(auto, trigger), tparams, rt, fn, xs, nonghost_callers_only, functype_opt, contract_opt, Some body, Static, Public) ->
              if List.mem_assoc fn funcmap || List.mem_assoc fn lems then static_error l "Duplicate function name." None;
              if List.mem_assoc fn tenv then static_error l "Local lemma name hides existing local variable name." None;
              let fterm = get_unique_var_symb fn (PtrType Void) in
              ((fn, (auto, trigger, fterm, l, tparams, rt, xs, nonghost_callers_only, functype_opt, contract_opt, body))::lems, predinsts, localpreds, localpredinsts)
            | _ -> static_error l "Local declarations must be lemmas or predicate family instances." None
          end
          ([], [], [], [])
          ds
      in
      let (lems, predinsts, localpreds, localpredinsts) = (List.rev lems, List.rev predinsts, List.rev localpreds, List.rev localpredinsts) in
      let funcnameterms' =
        List.map
          (fun (fn, (autom, trigger, fterm, l, tparams, rt, xs, nonghost_callers_only, functype_opt, contract_opt, body)) -> (fn, fterm))
        lems
      in
      let env = funcnameterms' @ env in
      let ghostenv = List.map (fun (fn, _) -> fn) funcnameterms' @ ghostenv in
      let tenv = List.map (fun (fn, _) -> (fn, PtrType Void)) funcnameterms' @ tenv in
      let env = List.map (fun (p, (l, ts, inputParamCount, ptype, psymb)) -> (p, psymb)) localpreds @ env in
      let ghostenv = List.map fst localpreds @ ghostenv in
      let tenv = List.map (fun (p, (l, ts, inputParamCount, ptype, psymb)) -> (p, ptype)) localpreds @ tenv in
      let predinstmap' =
        List.map
          begin fun ((p, (li, i)), (l, predinst_tparams, xs, body)) ->
            if not (List.mem_assoc i lems) then static_error li "Index of local predicate family instance must be lemma declared in same block." None;
            check_predinst (pn, ilist) tparams tenv env l p predinst_tparams [i] xs body
          end
          predinsts
      in
      let localpredinsts =
        localpredinsts |> List.map
          begin fun (p, (l, ts, inputParamCount, ptype, psymb, xs, body)) ->
            check_predinst0 [] 0 ts psymb inputParamCount (pn, ilist) tparams tenv env l p [] [] xs body
          end
      in
      let funcmap' =
        List.map
          begin fun (fn, (auto, trigger, fterm, l, tparams', rt, xs, nonghost_callers_only, functype_opt, contract_opt, body)) ->
            let (rt, xmap, functype_opt, pre, pre_tenv, post) =
              check_func_header pn ilist tparams tenv env l (Lemma(auto, trigger)) tparams' rt fn (Some fterm) xs nonghost_callers_only functype_opt contract_opt (Some body)
            in
            (fn, FuncInfo (env, Some fterm, l, Lemma(auto, trigger), tparams', rt, xmap, nonghost_callers_only, pre, pre_tenv, post, functype_opt, Some (Some body), Static, Public))
          end
          lems
      in
      let predinstmap = localpredinsts @ predinstmap' @ predinstmap in
      let funcmap = funcmap' @ funcmap in
      let verify_lems lems0 =
        List.fold_left
          begin fun lems0 (fn, FuncInfo (funenv, fterm, l, k, tparams', rt, xmap, nonghost_callers_only, pre, pre_tenv, post, functype_opt, Some (Some (ss, closeBraceLoc)), _, _)) ->
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
              (function (fn, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, _, _)) -> [fn] | _ -> [])
              funcmap
          in
          ignore $. verify_lems lems0;
          None
        | Some (lems, g, indinfo) ->
          Some (verify_lems lems, g, indinfo)
      in
      check_block_declarations ss;
      let cont h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in      
      let cont h tenv env = free_locals closeBraceLoc h tenv env !locals_to_free cont in
      let return_cont h tenv env retval = free_locals closeBraceLoc h tenv env !locals_to_free (fun h env -> return_cont h tenv env retval) in
      let lblenv = List.map (fun (lbl, lblcont) -> (lbl, (fun blocksdone sizemap tenv ghostenv h env -> free_locals closeBraceLoc h tenv env !locals_to_free (fun h env -> lblcont blocksdone sizemap tenv ghostenv h env)))) lblenv in
      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env -> cont h tenv env) return_cont econt
    | PureStmt (l, s) ->
      begin
        match s with
          PerformActionStmt (_, nonpure_ctxt, _, _, _, _, _, _, _, _, _, _, _, _, _, _) ->
          nonpure_ctxt := not pure
        | _ -> ()
      end;
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
    | GotoStmt (l, lbl) ->
      if pure then static_error l "goto statements are not allowed in a pure context" None;
      begin
        match try_assoc lbl lblenv with
          None -> static_error l "No such label." None
        | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | NoopStmt l -> cont h env
    | LabelStmt (l, _) -> static_error l "Label statements cannot appear in this position." None
    | InvariantStmt (l, _) -> static_error l "Invariant statements cannot appear in this position." None
    | Break l ->
      begin match try_assoc "#break" lblenv with
        None -> static_error l "Unexpected break statement" None
      | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | SuperConstructorCall(l, es) -> static_error l "super must be first statement of constructor." None
  and
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt
        ) return_cont econt
      )
  and
  
  (* Region: verification of blocks *)
  
    goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block =
    let `Block (inv, ss, cont) = block in
    let l() =
      match (inv, ss) with
        (Some (l, _, _), _) -> l
      | (_, s::_) -> stmt_loc s
      | _ -> assert false (* A block that has no invariant and no body cannot be in a loop *)
    in
    begin
      match (List.memq block blocks_done, inv) with
        (true, _) when pure -> assert_false h env (l()) "Loops are not allowed in a pure context." None
      | (true, None) -> assert_false h env (l()) "Loop invariant required." None
      | (_, Some (l, inv, tenv)) ->
        consume_asn rules [] h ghostenv env inv true real_unit (fun _ h _ _ _ ->
          check_leaks h env l "Loop leaks heap chunks."
        )
      | (false, None) ->
        let blocks_done = block::blocks_done in
        verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont econt
    end
  and verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env explicit l eo epilog return_cont econt =
    with_context (Executing (h, env, l, "Executing return statement")) $. fun () ->
    if explicit then check_breakpoint h env l;
    if pure && not (List.mem "#result" ghostenv) then static_error l "Cannot return from a regular function in a pure context." None;
    begin fun cont ->
      match eo with
        None -> cont h None
      | Some e ->
        if not pure then check_ghost ghostenv l e;
        let tp = match try_assoc "#result" tenv with None -> static_error l "Void function cannot return a value: " None | Some tp -> tp in
        let w = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e tp in
        verify_expr false (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env None w (fun h env v ->
        cont h (Some v)) econt
    end $. fun h retval ->
    begin fun cont ->
      if not pure && unloadable then
        let codeCoef = List.assoc "currentCodeFraction" env in
        let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
        produce_chunk h (module_code_symb, true) [] codeCoef (Some 1) [current_module_term] None cont
      else
        cont h
    end $. fun h ->
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env epilog cont (fun _ _ -> assert false) econt
    end $. fun sizemap tenv ghostenv h env ->
    return_cont h tenv env retval
  and
    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt =
    let (decls, ss) =
      let rec iter decls ss =
        match ss with
          (DeclStmt _) as s::ss -> iter (s::decls) ss
        | _ -> (List.rev decls, ss)
      in
      iter [] ss
    in
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env decls cont return_cont econt
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
              let (inv, tenv) = check_asn (pn,ilist) tparams tenv inv in
              (Some (l, inv, tenv), ss)
            in
            match ss with
              (PureStmt (_, InvariantStmt (l, inv)))::ss -> some_inv l inv ss
            | InvariantStmt (l, inv)::ss ->
              if not pure then static_error l "Invariant statements must be inside an annotation." None;
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
            | block'::_ -> goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block'
          in
          let block' = `Block (inv, ss, cont) in
          let lblenv =
            let cont blocks_done sizemap tenv ghostenv h env =
              goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block'
            in
            let rec iter lblenv lbls =
              match lbls with
                [] -> lblenv
              | (l, lbl)::lbls ->
                if List.mem_assoc lbl lblenv then static_error l "Duplicate label" None;
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
      | block0::_ -> goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block0
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
                      [(x, get_unique_var_symb_ x t (List.mem x ghostenv))]
                    else
                      [(x, v)]
                end
                env
            in
            produce_asn [] [] ghostenv env inv real_unit None None (fun h ghostenv env ->
              let blocks_done = block::blocks_done in
              verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont econt
            )
        end
        blocks
    end
  and verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt =
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
          let epilog = List.map (function (PureStmt (l, s)) -> s | s -> static_error (stmt_loc s) "An epilog statement must be a pure statement." None) epilog in
          verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env true lr eo epilog return_cont econt
        in
        (ss, tcont)
      else
        (ss, tcont)
    in
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt
  
  (* Region: verification of function bodies *)
  and create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams' =
    match (pre, post) with
    (ExprAsn(_, pre), ExprAsn(_, post)) ->
      List.iter
        begin fun (x, tp) ->
          if not (is_universal_type tp) then
            static_error l
              begin
                Printf.sprintf
                  begin
                    "This auto lemma is not supported because VeriFast currently uses an untyped underlying logic, \
                     and the type of parameter '%s' is not isomorphic to the logic's universe. A type is isomorphic \
                     if it is infinite and its type arguments are isomorphic. \
                     You can work around this limitation by introducing explicit cast functions."
                  end
                  x
              end
              None
        end
        ps;
      ctxt#begin_formal;
      let xs = Array.init (List.length ps) (fun j -> ctxt#mk_bound j (typenode_of_type (snd (List.nth ps j)))) in
      let xs = Array.to_list xs in
      let Some(env) = zip (List.map fst ps) xs in
      let t_pre = eval None env pre in
      let t_post = eval None env post in
      let tps = (List.map (fun (x, t) -> (typenode_of_type t)) ps) in
      let trigger = (
      match trigger with
        None -> []
      | Some(trigger) -> 
          let (trigger, tp) = check_expr (pn,ilist) tparams' pre_tenv trigger in
          [eval None env trigger]
      ) in
      let body = ctxt#mk_implies t_pre t_post in
      ctxt#end_formal;
      ctxt#assume_forall trigger tps body
  | (WPredAsn(p_loc, p_ref, _, p_targs, p_args1, p_args2), _) when List.length ps = 0 && List.for_all (fun arg -> match arg with | VarPat(_) -> true | _ -> false) (p_args1 @ p_args2) && 
         List.length p_targs = List.length tparams' && (List.for_all (fun (tp, t) -> match (tp, t) with (x, TypeParam(y)) when x = y -> true | _ -> false) (zip2 tparams' p_targs)) ->
      (Hashtbl.add auto_lemmas (p_ref#name) (None, tparams', List.map (fun (VarPat(x)) -> x) p_args1, List.map (fun (VarPat(x)) -> x) p_args2, pre, post))
  | (CoefAsn(loc, VarPat(f), WPredAsn(p_loc, p_ref, _, p_targs, p_args1, p_args2)), _) when List.length ps = 0 && List.for_all (fun arg -> match arg with | VarPat(_) -> true | _ -> false) (p_args1 @ p_args2) && 
         List.length p_targs = List.length tparams' && (List.for_all (fun (tp, t) -> match (tp, t) with (x, TypeParam(y)) when x = y -> true | _ -> false) (zip2 tparams' p_targs)) ->
      (Hashtbl.add auto_lemmas (p_ref#name) (Some(f), tparams', List.map (fun (VarPat(x)) -> x) p_args1, List.map (fun (VarPat(x)) -> x) p_args2, pre, post))
  | _ -> static_error l (sprintf "contract of auto lemma %s has wrong form" g) None
  and heapify_params h tenv env ps =
    begin match ps with
      [] -> (h, tenv, env)
    | (l, x, t, addr) :: ps -> 
      let xvalue = List.assoc x env in
      let tenv' = update tenv x (RefType (List.assoc x tenv)) in
      let h' = Chunk ((pointee_pred_symb l t, true), [], real_unit, [addr; xvalue], None) :: h in
      let env' = update env x addr in
      heapify_params h' tenv' env' ps
    end
  and cleanup_heapy_locals (pn, ilist) l h env ps cont =
    let rec cleanup_heapy_locals_core (pn, ilist) l h env ps cont= 
    match ps with
      [] -> cont h
    | (_, x, t, addr) :: ps ->
      consume_chunk rules h [] [] [] l (pointee_pred_symb l t, true) [] real_unit (TermPat real_unit) (Some 1) [TermPat addr; dummypat] (fun chunk h coef [_; t] size ghostenv env env' -> cleanup_heapy_locals_core (pn, ilist) l h env ps cont)
    in
    match ps with
      [] -> cont h
    | _ -> with_context (Executing (h, env, l, "Freeing parameters.")) (fun _ -> cleanup_heapy_locals_core (pn, ilist) l h env ps cont)
  and verify_func pn ilist lems boxes predinstmap funcmap tparams env l k tparams' rt g ps pre pre_tenv post ss closeBraceLoc =
    let tparams = tparams' @ tparams in
    let _ = push() in
    let penv = get_unique_var_symbs_ ps (match k with Regular -> false | _ -> true) in (* actual params invullen *)
    let heapy_vars = list_remove_dups (List.flatten (List.map (fun s -> stmt_address_taken s) ss)) in
    let heapy_ps = List.flatten (List.map (fun (x,tp) -> 
      if List.mem x heapy_vars then 
        let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType tp) in
        [(l, x, tp, addr)] 
      else 
       []
      ) (List.filter (fun (x, tp) -> List.mem_assoc x ps) pre_tenv))
    in
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
      if is_lemma k then 
        (true, Some (lems, g, indinfo), g::lems, List.map (function (p, t) -> p) ps @ ["#result"])
      else
        (false, None, lems, [])
    in
    let env = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] @ penv @ env in
    let _ =
      check_should_fail () $. fun _ ->
      produce_asn [] [] ghostenv env pre real_unit (Some (PredicateChunkSize 0)) None (fun h ghostenv env ->
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
          verify_cont (pn,ilist) [] [] tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env prolog tcont (fun _ _ -> assert false) (fun _ _ _ -> assert false)
        end $. fun sizemap tenv ghostenv h env ->
        begin fun cont ->
          if unloadable && not in_pure_context then
            let (_, _, _, _, module_code_symb, _) = List.assoc "module_code" predfammap in
            with_context (Executing (h, env, l, "Consuming code fraction")) $. fun () ->
            consume_chunk rules h [] [] [] l (module_code_symb, true) [] real_unit (SrcPat DummyPat) (Some 1) [TermPat current_module_term] $. fun _ h coef _ _ _ _ _ ->
            let half = real_mul l real_half coef in
            cont (Chunk ((module_code_symb, true), [], half, [current_module_term], None)::h) (("currentCodeFraction", RealType)::tenv) ("currentCodeFraction"::ghostenv) (("currentCodeFraction", half)::env)
          else
            cont h tenv ghostenv env
        end $. fun h tenv ghostenv env ->
        let do_return h env_post =
          consume_asn rules [] h ghostenv env_post post true real_unit (fun _ h ghostenv env size_first ->
            cleanup_heapy_locals (pn, ilist) closeBraceLoc h env heapy_ps (fun h ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            )
          )
        in
        let return_cont h tenv2 env2 retval =
          match (rt, retval) with
            (None, None) -> do_return h env
          | (Some tp, Some t) -> do_return h (("result", t)::env)
          | (None, Some _) -> assert_false h env l "Void function returns a value." None
          | (Some _, None) -> assert_false h env l "Non-void function does not return a value." None
        in
        begin fun tcont ->
          let (h,tenv,env) = heapify_params h tenv env heapy_ps in
          let outerlocals = ref [] in
          stmts_mark_addr_taken ss [(outerlocals, [])] (fun _ -> ());
          let body = if List.length !outerlocals = 0 then ss else [BlockStmt(l, [], ss, closeBraceLoc, outerlocals)] in
          verify_block (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont (fun _ _ _ -> assert false)
        end $. fun sizemap tenv ghostenv h env ->
        verify_return_stmt (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env false closeBraceLoc None [] return_cont (fun _ _ _ -> assert false)
      )
    in
    let _ = pop() in
    let _ = 
      (match k with
        Lemma(true, trigger) -> create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams'
      | _ -> ()
    ) in
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
      Some {cfds} -> cfds
    | None -> static_error lm ("No class was found: "^cn) None
  in
  
  let record_fun_timing l funName body =
    let time0 = Perf.time() in
    let result = body () in
    stats#recordFunctionTiming (string_of_loc l ^ ": " ^ funName) (Perf.time() -. time0);
    result
  in
  let rec verify_exceptional_return (pn,ilist) l h ghostenv env exceptp excep handlers =
    if not (is_unchecked_exception_type exceptp) then
      match handlers with
      | [] -> assert_false h env l ("Potentially unhandled exception " ^ (string_of_type exceptp) ^ ".") None 
      | (handler_tp, epost) :: handlers ->
        branch
          (fun () ->
            if (is_subtype_of_ exceptp handler_tp) || (is_subtype_of_ handler_tp exceptp) then
              consume_asn rules [] h ghostenv env epost true real_unit (fun _ h ghostenv env size_first -> ())
          )
          (fun () ->
            if not (is_subtype_of_ exceptp handler_tp) then
              verify_exceptional_return (pn,ilist) l h ghostenv env exceptp excep handlers
          )
  in
  let rec verify_cons (pn,ilist) cfin cn superctors boxes lems cons =
    match cons with
      [] -> ()
    | (sign, (lm, xmap, pre, pre_tenv, post, epost, ss, v))::rest ->
      match ss with
        None ->
        let (((_, p), _, _), ((_, _), _, _)) = lm in 
        if Filename.check_suffix p ".javaspec" then
          verify_cons (pn,ilist) cfin cn superctors boxes lems rest
        else
          static_error lm "Constructor specification is only allowed in javaspec files!" None
      | Some (Some (ss, closeBraceLoc)) ->
        record_fun_timing lm (cn ^ ".<ctor>") begin fun () ->
        if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying constructor %s\n" (Perf.time()) (string_of_loc lm) (string_of_sign (cn, sign));
        push();
        let env = get_unique_var_symbs_non_ghost ([(current_thread_name, current_thread_type)] @ xmap) in
        let (sizemap, indinfo) = switch_stmt ss env in
        let (ss, explicitsupercall) = match ss with SuperConstructorCall(l, es) :: body -> (body, Some(SuperConstructorCall(l, es))) | _ -> (ss, None) in
        let (in_pure_context, leminfo, ghostenv) = (false, None, []) in
        begin
          produce_asn [] [] ghostenv env pre real_unit None None $. fun h ghostenv env ->
          let this = get_unique_var_symb "this" (ObjType cn) in
          begin fun cont ->
            if cfin = FinalClass then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [this]) (List.assoc cn classterms)) cont else cont ()
          end $. fun () ->
          let do_body h ghostenv env =
            let do_return h env_post =
              consume_asn rules [] h ghostenv env_post post true real_unit $. fun _ h ghostenv env size_first ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            in
            let return_cont h tenv2 env2 retval =
              assert (retval = None);
              do_return h env
            in
            let econt throwl h env2 exceptp excep =
              verify_exceptional_return (pn,ilist) throwl h ghostenv env exceptp excep epost
            in
            let tenv = ("this", ObjType cn):: (current_thread_name, current_thread_type) ::pre_tenv in
            begin fun cont ->
              if cn = "java.lang.Object" then
                cont h
              else
                let (argtypes, args) = match explicitsupercall with
                  None -> ([], [])
                | Some(SuperConstructorCall(l, es)) -> 
                  ((List.map (fun e -> let (w, tp) = check_expr (pn,ilist) [] tenv e in tp) es), es)
                in
                match try_assoc argtypes superctors with
                  None ->
                  static_error lm "There is no superclass constructor that matches the superclass constructor call" None
                | Some (lc0, xmap0, pre0, pre_tenv0, post0, epost0, _, v0) ->
                  with_context (Executing (h, env, lm, "Implicit superclass constructor call")) $. fun () ->
                  let eval_h h env e cont = verify_expr false (pn,ilist) [] false leminfo funcmap sizemap tenv ghostenv h env None e cont econt in
                  let pats = (List.map (fun e -> SrcPat (LitPat e)) args) in
                  verify_call funcmap eval_h lm (pn, ilist) None None [] pats ([], None, xmap0, ["this", this], pre0, post0, Some(epost0), v0) false leminfo sizemap h [] tenv ghostenv env (fun h env _ ->
                  cont h) econt
            end $. fun h ->
            let fds = get_fields (pn,ilist) cn lm in
            let rec iter h fds =
              match fds with
                [] -> verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss
                     (fun sizemap tenv ghostenv h env -> return_cont h tenv env None) return_cont econt
              | (f, {ft=t; fbinding=binding; finit=init})::fds ->
                if binding = Instance then begin
                  match init with 
                    None ->
                    assume_field h cn f t Real this (default_value t) real_unit $. fun h ->
                    iter h fds
                  | Some(e) -> 
                    with_context (Executing (h, [], expr_loc e, "Executing field initializer")) $. fun () ->
                    verify_expr false (pn,ilist) [] false leminfo funcmap sizemap [(current_class, ClassOrInterfaceName cn); ("this", ObjType cn); (current_thread_name, current_thread_type)] ghostenv h [("this", this); (current_thread_name, List.assoc current_thread_name env)] None e (fun h _ initial_value ->
                      assume_field h cn f t Real this initial_value real_unit $. fun h ->
                      iter h fds
                    ) (fun throwl h env2 exceptp excep -> assert_false h env2 throwl ("Field initializers throws exception.") None)
                end else
                  iter h fds
            in
            iter h fds
          in
          assume_neq this (ctxt#mk_intlit 0) $. fun() -> do_body h ghostenv (("this", this)::env)
        end;
        pop()
        end;
        verify_cons (pn,ilist) cfin cn superctors boxes lems rest
  in
  
  let rec verify_meths (pn,ilist) cfin cabstract boxes lems meths=
    match meths with
      [] -> ()
    | ((g,sign), (l,gh, rt, ps,pre,pre_tenv,post,epost,pre_dyn,post_dyn,epost_dyn,sts,fb,v, _,abstract))::meths ->
      if abstract && not cabstract then static_error l "Abstract method can only appear in abstract class." None;
      match sts with
        None -> let (((_,p),_,_),((_,_),_,_))=l in 
          if (Filename.check_suffix p ".javaspec") || abstract then verify_meths (pn,ilist) cfin cabstract boxes lems meths
          else static_error l "Method specification is only allowed in javaspec files!" None
      | Some (Some (ss, closeBraceLoc)) ->
        record_fun_timing l g begin fun () ->
        if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying method %s\n" (Perf.time()) (string_of_loc l) g;
        if abstract then static_error l "Abstract method cannot have implementation." None;
        push();
        let (in_pure_context, leminfo, ghostenv) =
          match gh with
            Ghost -> (true, Some (lems, "<method>", None), List.map (function (p, t) -> p) ps @ ["#result"])
          | Real -> (false, None, [])
        in
        begin
          let env = get_unique_var_symbs_non_ghost (ps @ [(current_thread_name, current_thread_type)]) in (* actual params invullen *)
          begin fun cont ->
            if fb = Instance then
            begin
              let ("this", thisTerm)::_ = env in
              let ("this", ObjType cn)::_ = ps in
              (* CAVEAT: Remove this assumption once we allow subclassing. *)
              (* assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) $. fun () -> *)
              begin fun cont ->
                if cfin = FinalClass then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) cont else cont ()
              end $. fun () ->
              assume_neq thisTerm (ctxt#mk_intlit 0) (fun _ -> cont (("this", ObjType cn)::pre_tenv))
            end else cont pre_tenv
          end $. fun tenv ->
          let (sizemap, indinfo) = switch_stmt ss env in
          let tenv = match rt with None ->tenv | Some rt -> ("#result", rt)::tenv in
          produce_asn [] [] ghostenv env pre real_unit None None $. fun h ghostenv env ->
          let do_return h env_post =
            consume_asn rules [] h ghostenv env_post post true real_unit $. fun _ h ghostenv env size_first ->
            check_leaks h env closeBraceLoc "Function leaks heap chunks."
          in
          let return_cont h tenv2 env2 retval =
            match (rt, retval) with
              (None, None) -> do_return h env
            | (Some tp, Some t) -> do_return h (("result", t)::env)
            | (None, Some _) -> assert_false h env l "Void function returns a value." None
            | (Some _, None) -> assert_false h env l "Non-void function does not return a value." None
          in
          let econt throwl h env2 exceptp excep =
            verify_exceptional_return (pn,ilist) throwl h ghostenv env exceptp excep epost
          in
          let cont sizemap tenv ghostenv h env = return_cont h tenv env None in
          verify_block (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt
        end;
        pop()
        end;
        verify_meths (pn,ilist) cfin cabstract boxes lems meths
  in
  
  let rec verify_classes boxes lems classm=
    match classm with
      [] -> ()
    | (cn, {cl; cabstract; cfinal; cmeths; cctors; csuper; cpn; cilist})::classm ->
      let (superctors, superfinal) =
        if csuper = "" then ([], ExtensibleClass) else
          let {cctors; cfinal} = List.assoc csuper classmap in
          (cctors, cfinal)
      in
      if superfinal = FinalClass then static_error cl "Cannot extend final class." None;
      verify_cons (cpn, cilist) cfinal cn superctors boxes lems cctors;
      verify_meths (cpn, cilist) cfinal cabstract boxes lems cmeths;
      verify_classes boxes lems classm
  in
  
  let rec verify_funcs (pn,ilist)  boxes lems ds =
    match ds with
     [] -> (boxes, lems)
    | Func (l, Lemma(auto, trigger), _, rt, g, ps, _, _, _, None, _, _)::ds -> 
      let g = full_name pn g in
      let (((_, g_file_name), _, _), _) = l in
      if language = Java && not (Filename.check_suffix g_file_name ".javaspec") then
        static_error l "A lemma function outside a .javaspec file must have a body. To assume a lemma, use the body '{ assume(false); }'." None;
      if auto && (Filename.check_suffix g_file_name ".c" or is_import_spec) then begin
        let FuncInfo ([], fterm, l, k, tparams', rt, ps, nonghost_callers_only, pre, pre_tenv, post, x, y,fb,v) = (List.assoc g funcmap) in
        register_prototype_used l g;
        create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams'
      end;
      verify_funcs (pn,ilist)  boxes (g::lems) ds
    | Func (l, k, _, _, g, _, _, functype_opt, _, Some _, _, _)::ds when k <> Fixpoint ->
      let g = full_name pn g in
      let lems' =
      record_fun_timing l g begin fun () ->
      if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying function %s\n" (Perf.time()) (string_of_loc l) g;
      let FuncInfo ([], fterm, l, k, tparams', rt, ps, nonghost_callers_only, pre, pre_tenv, post, _, Some (Some (ss, closeBraceLoc)),fb,v) = (List.assoc g funcmap)in
      let tparams = [] in
      let env = [] in
      verify_func pn ilist lems boxes predinstmap funcmap tparams env l k tparams' rt g ps pre pre_tenv post ss closeBraceLoc
      end in
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
                    None -> static_error l "No such action." None
                  | Some (_, apmap, pre, post) ->
                    let _ =
                      let rec iter ys xs =
                        match xs with
                          [] -> ()
                        | x::xs ->
                          if List.mem_assoc x boxvarmap then static_error l "Action parameter name clashes with box variable." None;
                          if List.mem_assoc x pmap then static_error l "Action parameter name clashes with handle predicate parameter." None;
                          if List.mem x ys then static_error l "Duplicate action parameter." None;
                          if startswith x "old_" then static_error l "Action parameter name cannot start with old_." None;
                          iter (x::ys) xs
                      in
                      iter [] xs
                    in
                    let apbs =
                      match zip xs apmap with
                        None -> static_error l "Incorrect number of action parameters." None
                      | Some bs -> bs
                    in
                    let apmap' = List.map (fun (x, (_, t)) -> (x, t)) apbs in
                    let tenv = boxvarmap @ old_boxvarmap @ pmap @ apmap' in
                    push();
                    let currentThread = get_unique_var_symb "currentThread" IntType in
                    let actionHandle = get_unique_var_symb "actionHandle" HandleIdType in
                    let predicateHandle = get_unique_var_symb "predicateHandle" HandleIdType in
                    assume (ctxt#mk_not (ctxt#mk_eq actionHandle predicateHandle)) begin fun () ->
                      let pre_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb ("old_" ^ x) t)) boxpmap in
                      with_context (Executing ([], [], l, "Checking preserved_by clause.")) $. fun () ->
                        with_context PushSubcontext $. fun () ->
                          produce_asn [] [] [] pre_boxargs boxinv real_unit None None $. fun _ _ pre_boxvars ->
                            let old_boxvars = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxvars in
                            let post_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) boxpmap in
                            produce_asn [] [] [] post_boxargs boxinv real_unit None None $. fun _ _ post_boxvars ->
                              with_context PopSubcontext $. fun () ->
                                let hpargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) pmap in
                                let aargs = List.map (fun (x, (y, t)) -> (x, y, get_unique_var_symb x t)) apbs in
                                let apre_env = List.map (fun (x, y, t) -> (y, t)) aargs in
                                let ghostenv = List.map (fun (x, t) -> x) tenv in
                                assume (eval None ([("actionHandle", actionHandle)] @ pre_boxvars @ apre_env) pre) $. fun () ->
                                  assume (eval None ([("predicateHandle", predicateHandle)] @ pre_boxvars @ hpargs) inv) $. fun () ->
                                    assume (eval None ([("actionHandle", actionHandle)] @ post_boxvars @ old_boxvars @ apre_env) post) $. fun () ->
                                      let aarg_env = List.map (fun (x, y, t) -> (x, t)) aargs in
                                      let env = ["actionHandle", actionHandle; "predicateHandle", predicateHandle; "currentThread", currentThread] @
                                        post_boxvars @ old_boxvars @ aarg_env @ hpargs in
                                      let tenv = ["actionHandle", HandleIdType; "predicateHandle", HandleIdType; "currentThread", IntType] @ tenv in
                                      verify_cont (pn,ilist) [] [] [] boxes true leminfo funcmap predinstmap [] tenv ghostenv [] env ss begin fun _ _ _ _ _ ->
                                        let post_inv_env = [("predicateHandle", predicateHandle)] @ post_boxvars @ hpargs in
                                        assert_expr_split inv [] post_inv_env l "Handle predicate invariant preservation check failure." None
                                      end begin fun _ _ -> static_error l "Return statements are not allowed in handle predicate preservation proofs." None end
                                      begin fun _ _ _ _ _ -> static_error l "Exceptions are not allowed in handle predicate preservation proofs." None end
                    end;
                    pop();
                    an
                  end)
               pbcs
           in
           List.iter (fun (an, _) -> if not (List.mem an pbcans) then static_error l ("No preserved_by clause for action '" ^ an ^ "'.") None) amap)
        hpmap;
      verify_funcs (pn,ilist)  (bcn::boxes) lems ds
    | _::ds -> verify_funcs (pn,ilist)  boxes lems ds
  in
  let lems0 =
    flatmap
      (function (g, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, fb, v)) -> [g] | _ -> [])
      funcmap0
  in
  let rec verify_funcs' boxes lems ps=
    match ps with
      PackageDecl(l,pn,il,ds)::rest-> let (boxes, lems) = verify_funcs (pn,il) boxes lems ds in verify_funcs' boxes lems rest
    | [] -> verify_classes boxes lems classmap
  in
  verify_funcs' [] lems0 ps;
  
  ((prototypes_implemented, !functypes_implemented), (structmap1, enummap1, globalmap1, inductivemap1, purefuncmap1,predctormap1, malloc_block_pred_map1, field_pred_map1, predfammap1, predinstmap1, typedefmap1, functypemap1, funcmap1, boxmap,classmap1,interfmap1,classterms1,interfaceterms1, pluginmap1))
  
  in (* let rec check_file *)
  
  (* Region: top-level stuff *)
  
  let jardeps = ref [] in
  let provide_files = ref [] in
  let (prototypes_implemented, functypes_implemented) =
    let (headers, ds)=
      match file_type path with
        | Java ->
          let l = file_loc path in
          let (headers, javas, provides) =
            if Filename.check_suffix path ".jarsrc" then
              let (jars, javas, provides) = parse_jarsrc_file_core path in
              let specPath = Filename.chop_extension path ^ ".jarspec" in
              let jarspecs = List.map (fun path -> (l, path ^ "spec")) jars in (* Include the location where the jar is referenced *)
              if Sys.file_exists specPath then begin
                let (specJars, _) = parse_jarspec_file_core specPath in
                jardeps := specJars @ jars;
                ((l, specPath) :: jarspecs, javas, provides)
              end else
                (jarspecs, javas, provides)
            else
              ([], [path], [])
          in
          let provides = provides @ options.option_provides in
          let token = (* A string to make the provide files unique *)
            if options.option_keep_provide_files then "" else Printf.sprintf "_%ld" (Stopwatch.getpid ())
          in
          let provide_javas =
            provides |> imap begin fun i provide ->
              let provide_file = Printf.sprintf "%s_provide%d%s.java" (Filename.chop_extension path) i token in
              let cmdLine = Printf.sprintf "%s > %s" provide provide_file in
              let exitCode = Sys.command cmdLine in
              if exitCode <> 0 then
                raise (static_error l (Printf.sprintf "Provide %d: command '%s' failed with exit code %d" i cmdLine exitCode) None);
              provide_file
            end
          in
          provide_files := provide_javas;
          let javas = javas @ provide_javas in
          let ds = List.map (fun x -> parse_java_file x reportRange reportShouldFail) javas in
          (headers, ds)
        | CLang ->
          if Filename.check_suffix path ".h" then
            parse_header_file "" path reportRange reportShouldFail
          else
            parse_c_file path reportRange reportShouldFail options.option_run_preprocessor
    in
    emitter_callback ds;
    let result =
      check_should_fail ([], []) $. fun () ->
      let (linker_info, _) = check_file path false true programDir headers ds in
      linker_info
    in
    begin
      match !shouldFailLocs with
        [] -> ()
      | l::_ -> static_error l "No error found on line." None
    end;
    result
  in
  
  if not options.option_keep_provide_files then begin
    !provide_files |> List.iter Sys.remove
  end;
  
  stats#appendProverStats ctxt#stats;

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
      List.map (fun line -> ".requires " ^ line) (sorted_lines !prototypes_used)
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
  if file_type path <> Java then
    create_manifest_file()
  else
    if Filename.check_suffix path ".jarsrc" then
      create_jardeps_file()

(* Region: prover selection *)

let verify_program_with_stats (* ?verify_program_with_stats *)
    ?(emitter_callback : package list -> unit = fun _ -> ())
    ctxt
    (print_stats : bool)
    (verbose : options)
    (path : string)
    (reportRange : range_kind -> loc -> unit)
    (reportUseSite : decl_kind -> loc -> loc -> unit)
    (breakpoint : (string * int) option) : unit =
  do_finally
    (fun () -> verify_program_core ~emitter_callback:emitter_callback ctxt verbose path reportRange reportUseSite breakpoint)
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
  "VeriFast " ^ Vfversion.version ^ " for C and Java (released " ^ Vfversion.release_date ^ ") <http://www.cs.kuleuven.be/~bartj/verifast/>\n" ^
  "By Bart Jacobs <http://www.cs.kuleuven.be/~bartj/>, Jan Smans <http://www.cs.kuleuven.be/~jans/>, and Frank Piessens, with contributions by Cedric Cuypers, Lieven Desmet, Jan Tobias Muehlberg, Willem Penninckx, Pieter Philippaerts, Thomas Van Eyck, and Frederic Vogels" ^
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
      
let verify_program (* ?verify_program *)
    ?(emitter_callback : package list -> unit = fun _ -> ())
    (prover : string option)
    (print_stats : bool)
    (options : options)
    (path : string)
    (reportRange : range_kind -> loc -> unit)
    (reportUseSite : decl_kind -> loc -> loc -> unit)
    (breakpoint : (string * int) option) : unit =
  lookup_prover prover
    (object
       method run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> unit =
         fun ctxt -> verify_program_with_stats ~emitter_callback:emitter_callback ctxt print_stats options path reportRange reportUseSite breakpoint
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

exception FileNotFound

let read_file_lines path =
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
  else raise FileNotFound

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
      let manifest_path = 
        try Filename.chop_extension modulepath ^ ".vfmanifest" with
          Invalid_argument  _ -> raise (CompilationError "file without extension")
      in
      let lines =
        if List.mem_assoc manifest_path !manifest_map then
          List.assoc manifest_path !manifest_map
        else
          try
            read_file_lines manifest_path
          with FileNotFound ->
            try
              read_file_lines (Filename.concat bindir manifest_path)
            with FileNotFound ->
              failwith ("VeriFast link phase error: could not find .vfmanifest file '" ^ manifest_path ^ "' for module '" ^ modulepath ^ "'. Re-verify the module using the -emit_vfmanifest option.")
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
  let mainModuleName = try Filename.chop_extension (Filename.basename mainModulePath) with Invalid_argument _ -> raise (CompilationError "file without extension") in
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
        let lines = try read_file_lines exportPath with FileNotFound -> failwith ("Could not find export manifest file '" ^ exportPath ^ "'") in
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
