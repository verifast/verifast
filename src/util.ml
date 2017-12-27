open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)

(* Region: General-purpose utility functions *)

let input_fully c =
  let buf = Bytes.create 60000 in
  let b = Buffer.create 60000 in
  let rec iter () =
    let n = input c buf 0 60000 in
    if n = 0 then
      Buffer.contents b
    else begin
      Buffer.add_subbytes b buf 0 n;
      iter ()
    end
  in
  iter ()

let push x rxs = rxs := x::!rxs

let string_map f s =
  let n = String.length s in
  let result = Bytes.create n in
  for i = 0 to n - 1 do
    Bytes.set result i (f s.[i])
  done;
  Bytes.unsafe_to_string result

let num_of_ints p q = div_num (num_of_int p) (num_of_int q)

let num_of_decimal_fraction s =
  let n = String.length s in
  let mantissa = Buffer.create n in
  let decimal_places = ref 0 in
  let exponent = ref 0 in
  let offset = ref 0 in
  let next () =
    if !offset = n then '\000' else s.[!offset]
  in
  let eat () = incr offset in
  let mk_num () =
    num_of_string (Buffer.contents mantissa) */ (num_of_int 10 **/ (num_of_int !exponent -/ num_of_int !decimal_places))
  in
  let parse_exponent () =
    if next () = '+' then eat ();
    exponent := int_of_string (String.sub s !offset (n - !offset));
    mk_num ()
  in
  let rec parse_fractional_part () =
    match next () with
      '0'..'9' as c -> eat (); Buffer.add_char mantissa c; incr decimal_places; parse_fractional_part ()
    | 'e'|'E' -> eat (); parse_exponent ()
    | '\000' -> mk_num ()
  in
  let rec parse () =
    match next () with
      '0'..'9' as c -> eat (); Buffer.add_char mantissa c; parse ()
    | '.' -> eat (); parse_fractional_part ()
    | 'e'|'E' -> eat (); parse_exponent ()
    | '\000' -> mk_num ()
  in
  parse ()

(** Same as fprintf followed by a flush. *)
let fprintff format = kfprintf (fun chan -> flush chan) format
(** Same as printf followed by a flush. *)
let printff format = fprintff stdout format

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

let rec try_assoc_case_insensitive x xys =
  let x = String.uppercase_ascii x in
  let rec iter xys =
    match xys with
      [] -> None
    | (x', y)::xys when String.uppercase_ascii x' = x -> Some y
    | _::xys -> iter xys
  in
  iter xys

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

let split separator_predicate string =
  let n = String.length string in
  let rec iter parts start k =
    let current_part () = String.sub string start (k - start) in
    if k = n then
      List.rev (current_part ()::parts)
    else
      if separator_predicate string.[k] then
        iter (current_part ()::parts) (k + 1) (k + 1)
      else
        iter parts start (k + 1)
  in
  iter [] 0 0

let split_around_char string char =
  try 
    let index = String.rindex string char in
    (String.sub string 0 index, String.sub string (index + 1) ((String.length string) - index - 1))
  with 
    _ -> (string, "")
    
let rec chars_of_string s = 
  match s with 
  | "" -> [] 
  | s -> (String.get s 0 )::(chars_of_string (String.sub s 1 ((String.length s) - 1)))

let concat path1 path2 =
  if path1 = "" || path1 = "." then path2 else path1 ^ Filename.dir_sep ^ path2

let default_bindir = Filename.dirname Sys.executable_name
let bindir = ref default_bindir
let set_bindir dir =
  bindir := dir

let rtdir _ = concat !bindir "rt"
let cwd = Sys.getcwd()

let compose base path = if Filename.is_relative path then base ^ "/" ^ path else path

(** Reduces './foo' to 'foo', 'foo/.' to 'foo', 'foo//' to 'foo/', and 'foo/../bar' to 'bar'. *)
let reduce_path path =
  let path = split (fun c -> c = '/' || c = '\\') path in
  let rec iter reduced todo =
    match reduced, todo with
      _, [] -> if reduced = [] then "." else String.concat "/" (List.rev reduced)
    | head::reduced, ".."::todo when head <> ".." && head <> "" -> iter reduced todo
    | _, "."::todo -> iter reduced todo
    | _::_, ""::todo -> iter reduced todo
    | _, part::todo -> iter (part::reduced) todo
  in
  iter [] path

let abs_path path = 
  if Filename.is_relative path then 
    reduce_path (compose cwd path) 
  else 
    path

(* Like reduce_path, except does not remove the first component *)
let reduce_rooted_path path =
  let root::path = split (fun c -> c = '/' || c = '\\') path in
  let rec iter reduced todo =
    match reduced, todo with
      _, [] -> String.concat "/" (root::List.rev reduced)
    | head::reduced, ".."::todo when head <> ".." && head <> "" -> iter reduced todo
    | _, "."::todo -> iter reduced todo
    | _::_, ""::todo -> iter reduced todo
    | _, part::todo -> iter (part::reduced) todo
  in
  iter [] path

let remove_prefix p s =
  let np = String.length p in
  let ns = String.length s in
  if np <= ns && String.sub s 0 np = p then
    Some (String.sub s np (ns - np))
  else
    None

let crt_vroot path = ("CRT", reduce_path path)

let replace_vroot vroots path =
  let root::rest = split (fun c -> c = '/' || c = '\\') path in
  match try_assoc root vroots with
  | Some p -> (String.concat "/" (p::rest))
  | None -> path

let qualified_path vroots modpath (basedir, relpath) =
  if (replace_vroot vroots relpath) <> relpath then relpath else
  let module_basedir = reduce_path (compose cwd (Filename.dirname modpath)) in
  let module_basedir_prefix = module_basedir ^ "/" in
  let path = reduce_path (compose cwd (basedir ^ "/" ^ relpath)) in
  let vrooted_paths = vroots |> flatmap begin fun (name, expansion) ->
      match remove_prefix (expansion ^ "/") path with
        Some relpath -> [name ^ "/" ^ relpath]
      | None -> []
    end
  in
  match vrooted_paths with
    h::t -> h
  | [] ->
  match remove_prefix module_basedir_prefix path with
    Some relpath -> "./" ^ relpath
  | None ->
  let mcs = split (fun c -> c = '/') module_basedir in
  let pcs = split (fun c -> c = '/') path in
  if List.hd mcs <> List.hd pcs then
    (* We're running on Windows and the path is on a different drive than the module. Use an absolute path. *)
    path
  else
  let rec iter mcs pcs =
    match mcs, pcs with
      mc::mcs1, pc::pcs1 when mc = pc -> iter mcs1 pcs1
    | _ -> "./" ^ String.concat "/" (list_make (List.length mcs) ".." @ pcs)
  in
  iter mcs pcs
