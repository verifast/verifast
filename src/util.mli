val num_of_ints : int -> int -> Num.num
val fprintff : out_channel -> ('a, out_channel, unit, unit) format4 -> 'a
val printff : ('a, out_channel, unit, unit) format4 -> 'a
val manifest_map : (string * string list) list ref
val jardeps_map : (string * string list) list ref
val option_map : ('a -> 'b) -> 'a option -> 'b option
val zip : 'a list -> 'b list -> ('a * 'b) list option
val zip2 : 'a list -> 'b list -> ('a * 'b) list
val do_finally : (unit -> 'a) -> (unit -> 'b) -> 'a
val ( $. ) : ('a -> 'b) -> 'a -> 'b
val ( |> ) : 'a -> ('a -> 'b) -> 'b
val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val for_all_take2 : ('a -> 'b -> bool) -> int -> 'a list -> 'b list -> bool
val intersect : 'a list -> 'a list -> 'a list
val flatmap : ('a -> 'b list) -> 'a list -> 'b list
val head_flatmap : ('a -> 'b list) -> 'a list -> 'b option
val head_flatmap_option : ('a -> 'b option) -> 'a list -> 'b option
val extract : ('a -> 'b option) -> 'a list -> ('b * 'a list) option
val drop : int -> 'a list -> 'a list
val take : int -> 'a list -> 'a list
val take_drop : int -> 'a list -> 'a list * 'a list
val list_make : int -> 'a -> 'a list
val remove : ('a -> bool) -> 'a list -> 'a list
val distinct : 'a list -> bool
val index_of : 'a -> 'a list -> int -> int option
val try_assoc : 'a -> ('a * 'b) list -> 'b option
val try_assoc0 : 'a -> ('a * 'b) list -> ('a * 'b) option
val try_assq : 'a -> ('a * 'b) list -> 'b option
val try_assoc_i : 'a -> ('a * 'b) list -> (int * 'b) option
val imap : (int -> 'a -> 'b) -> 'a list -> 'b list
val list_remove_dups : 'a list -> 'a list
val try_find : ('a -> bool) -> 'a list -> 'a option
val try_extract : 'a list -> ('a -> bool) -> ('a * 'a list) option
val startswith : string -> string -> bool
val chop_suffix : string -> string -> string option
val chop_suffix_opt : string -> string -> string
val split : (char -> bool) -> string -> string list
val reduce_path : string -> string
val concat : string -> string -> string
val try_assoc2 : 'a -> ('a * 'b) list -> ('a * 'b) list -> 'b option
val assoc2 : 'a -> ('a * 'b) list -> ('a * 'b) list -> 'b
exception IsNone
val get : 'a option -> 'a
val bindir : string
val rtdir : string
