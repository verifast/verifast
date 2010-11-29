open Format
open Big_int

type sexpression =
  | List of sexpression list
  | Symbol of string
  | Keyword of string
  | Number of big_int

type argument_group =
  | Single of sexpression
  | KeywordPair of string * sexpression

let rec group_arguments : sexpression list -> argument_group list = function
  | (Keyword kw :: x :: xs) -> KeywordPair (kw, x) :: group_arguments xs
  | (x :: xs)               -> Single x :: group_arguments xs
  | []                      -> []

let ($) f x = f x

let seq (fs : (unit -> unit) list) () : unit =
  let invoke f = f ()
  in
  List.iter invoke fs

let destructure sexpressions : sexpression list * (sexpression * sexpression) list =
  let rec group_kw_args args acc sexprs =
    match sexprs with
      | []                                 -> (args, List.rev acc)
      | ((Keyword _) as kw :: v :: sexprs) -> group_kw_args args ((kw, v) :: acc) sexprs
      | _                                  -> failwith "Invalid s-expression"
  in
  let rec group_args acc sexprs =
    match sexprs with
      | []                         -> (List.rev acc, [])
      | (Keyword _ :: _) as sexprs -> group_kw_args (List.rev acc) []  sexprs
      | (sexpr :: sexprs)          -> group_args (sexpr :: acc) sexprs
  in
  group_args [] sexpressions

let format_sexpression formatter sexpr =
  let box ?(indent = 0) (contents : unit -> unit) () : unit =
    pp_open_box formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let hbox (contents : unit -> unit) () =
    pp_open_hbox formatter ();
    contents ();
    pp_close_box formatter ()
  in
  let vbox ?(indent = 0) (contents : unit -> unit) () =
    pp_open_vbox formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let hvbox ?(indent = 0) (contents : unit -> unit) () : unit =
    pp_open_hvbox formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let hovbox ?(indent = 0) (contents : unit -> unit) () : unit =
    pp_open_hovbox formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let verbatim str : unit -> unit =
    box $ fun () -> pp_print_string formatter str
  in
  let flush () : unit =
    pp_print_flush formatter ()
  in
  let space () : unit =
    pp_print_space formatter ()
  in
  let break x y () : unit =
    pp_print_break formatter x y
  in
  let nop () =
    ()
  in
  let separate_by_spaces xs () : unit =
    let separate xs =
      List.iter (fun x -> seq [ space; x ] ()) xs
    in
    match xs with
      | []      -> ()
      | [x]     -> x ()
      | (x::xs) -> x (); separate xs
  in
  let rec format sexpr : unit -> unit =
    match sexpr with
      | Symbol str ->
        if String.length str = 0
        then verbatim "||"
        else verbatim str
      | Keyword str -> verbatim $ ":" ^ str
      | Number n    -> verbatim $ string_of_big_int n
      | List xs     ->
        match xs with
          | [ Symbol "quote"; quoted ] -> hbox $ seq [ verbatim "'"
                                                     ; format quoted ]
          | _ ->
            hbox $ seq [ verbatim "("
                       ; begin
                         match xs with
                           | []        -> nop
                           | [x]       -> box $ format x
                           | [x; y]    -> hvbox $ seq [ format x
                                                      ; break 1 2
                                                      ; format y ]
                           | (x :: xs) ->
                             let (args, kw_args) = destructure xs
                             in
                             let args' =
                               hovbox $ separate_by_spaces (List.map format args)
                             in
                             let kw_args' =
                               let format_pair (kw, sexpr) =
                                 hbox $ separate_by_spaces [ format kw
                                                           ; format sexpr ]
                               in
                               vbox $ separate_by_spaces (List.map format_pair kw_args)
                             in
                             let is_empty xs =
                               xs = []
                             in
                             let sexprs =
                               List.concat
                                 [ [ format x ]
                                 ; if is_empty args
                                   then []
                                   else [ args' ]
                                 ; if is_empty kw_args
                                   then []
                                   else [ kw_args' ] ]
                             in
                             hvbox ~indent:2 $ separate_by_spaces sexprs
                         end
                       ; verbatim ")" ]
  in
  format sexpr ();
  flush ()

let string_of_sexpression ?(margin = 160) sexpr =
  let buffer = Buffer.create 1024 in
  let formatter = formatter_of_buffer buffer in
  pp_set_margin formatter margin;
  format_sexpression formatter sexpr;
  Buffer.contents buffer
