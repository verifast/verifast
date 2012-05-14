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

Mutable state & symbolic execution forks
========================================

VeriFast is written in a partially functional and partially imperative style. In particular,
the symbolic execution state (essentially the heap, the environment, and the path condition) is
partially threaded explicitly in functional style (the heap and the environment) and partially
kept in a mutable data structure (the path condition: it is kept as the state of the SMT solver).
Note: there are also some other pieces of mutable state linked to the symbolic execution state:
- the set of used symbol names (for generating fresh symbol names)
- the symbolic execution trace (for debugging)

Symbolic execution is forked at branching constructs, such as if statements, if assertions,
switch statements, switch assertions, while statements, blocks with gotos, shortcut boolean operators,
and many other places.

It is important that when a branch ends and the next branch is started, the symbolic execution state is
properly reset, i.e. all changes to the path condition, all newly allocated symbol names, etc. are forgotten.
This is done by using the push() and pop() functions, or, more structuredly, the in_temporary_context function.

There are two general strategies for when to push() and pop(): at the time of a change to the mutable state, or
at the time of the start of a branch.

Note: the following are some of the functions that change the mutable state:
- ctxt#assume
- get_unique_var_symb
- ctxt#assume_forall

Since it is impractical to push and pop whenever we call get_unique_var_symb, let us use as the strategy that ***we
push and pop whenever we start a new branch***. Nonetheless, for the sake of "defense in depth", use assume instead
of ctxt#assume etc. whenever it makes sense.

The codebase uses "effect typing" to help check that all branches are "protected" by push and pop. Specifically, each
function that potentially modifies the mutable state should have return type symexec_result, i.e. it should return
SymExecSuccess. To "cast" this type to unit, use function "execute_branch". This function saves and restores the
mutable state.


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

(** Eliminates '.' and 'foo/..' components. *)
let reduce_path path =
  let path = split (fun c -> c = '/' || c = '\\') path in
  let rec iter reduced todo =
    match reduced, todo with
      _, [] -> String.concat "/" (List.rev reduced)
    | _::reduced, ".."::todo -> iter reduced todo
    | _, "."::todo -> iter reduced todo
    | _, part::todo -> iter (part::reduced) todo
  in
  iter [] path

let concat path1 path2 =
  if path1 = "" || path1 = "." then path2 else path1 ^ Filename.dir_sep ^ path2

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
let rtdir = concat bindir "rt"
