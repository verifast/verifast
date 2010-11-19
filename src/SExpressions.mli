open Big_int


type sexpression =
  | List of sexpression list
  | Symbol of string
  | Keyword of string
  | Number of big_int

val format_sexpression : Format.formatter -> sexpression -> unit

val string_of_sexpression : sexpression -> string
