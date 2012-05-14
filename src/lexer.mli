val latin1_to_utf8 : string -> string
val utf8_byte_order_mark : string
val file_to_utf8 : string -> string
val utf8_to_file : string -> string
val get_first_line_tokens : string -> string list
type file_options = { file_opt_annot_char : char; file_opt_tab_size : int; }
val get_file_options : string -> file_options
val readFile : string -> string
type token =
    Kwd of string
  | Ident of string
  | Int of Big_int.big_int
  | RealToken of Big_int.big_int
  | Float of float
  | String of string
  | CharToken of char
  | PreprocessorSymbol of string
  | Eol
  | ErrorToken
type srcpos = (string * string) * int * int
type loc = srcpos * srcpos
val dummy_srcpos : (string * string) * int * int
val dummy_loc :
  ((string * string) * int * int) * ((string * string) * int * int)
exception ParseException of loc * string
module Stream :
  sig
    exception Failure
    exception Error of string
    type 'a t = (int -> 'a option) * int ref * 'a option list ref
    val from : 'a -> 'a * int ref * 'b list ref
    val of_list : 'a list -> ('b -> 'a option) * int ref * 'c list ref
    val peek : (int -> 'a) * int ref * 'a list ref -> 'a
    val junk : 'a * 'b * 'c list ref -> unit
    val push : 'a -> 'b * 'c * 'a list ref -> unit
    val empty : (int -> 'a option) * int ref * 'a option list ref -> unit
    val npeek : int -> 'a t -> 'a list
    val iter : ('a -> unit) -> 'a t -> unit
  end
val big_int_of_hex_string : string -> Big_int.big_int
type decl_kind = DeclKind_InductiveType
type range_kind =
    KeywordRange
  | GhostKeywordRange
  | GhostRange
  | GhostRangeDelimiter
  | CommentRange
  | ErrorRange
val string_of_range_kind : range_kind -> string
val make_lexer_core :
  string list ->
  string list ->
  string * string ->
  string ->
  (range_kind -> srcpos * ((string * string) * int * int) -> unit) ->
  bool ->
  bool ->
  bool ->
  (srcpos * ((string * string) * int * int) -> 'a) ->
  char ->
  (unit -> srcpos * ((string * string) * int * int)) * bool ref *
  (('b -> ((srcpos * ((string * string) * int * int)) * token) option) *
   int ref * 'c list ref) *
  bool ref * bool ref
val make_lexer :
  string list ->
  string list ->
  string * string ->
  string ->
  (range_kind -> srcpos * ((string * string) * int * int) -> unit) ->
  (srcpos * ((string * string) * int * int) -> 'a) ->
  (unit -> srcpos * ((string * string) * int * int)) * bool ref *
  (('b -> ((srcpos * ((string * string) * int * int)) * token) option) *
   int ref * 'c list ref)
val make_preprocessor :
  (string ->
   string ->
   (unit -> ((string * string) * int * int) * ((string * string) * int * int)) *
   bool ref *
   ((int -> ('a * token) option) * int ref * ('a * token) option list ref)) ->
  string ->
  string ->
  (unit -> ((string * string) * int * int) * ((string * string) * int * int)) *
  bool ref * (('b -> ('a * token) option) * int ref * 'c list ref)
