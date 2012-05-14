val common_keywords : string list
val ghost_keywords : string list
val c_keywords : string list
val java_keywords : string list
exception StaticError of Lexer.loc * string * string option
val static_error : Lexer.loc -> string -> string option -> 'a
exception CompilationError of string
val file_type : string -> Ast.language
val opt : ('a Lexer.Stream.t -> 'b) -> 'a Lexer.Stream.t -> 'b option
val comma_rep :
  (('a * Lexer.token) Lexer.Stream.t -> 'b) ->
  ('a * Lexer.token) Lexer.Stream.t -> 'b list
val rep_comma :
  (('a * Lexer.token) Lexer.Stream.t -> 'b) ->
  ('a * Lexer.token) Lexer.Stream.t -> 'b list
val rep : ('a Lexer.Stream.t -> 'b) -> 'a Lexer.Stream.t -> 'b list
val parse_angle_brackets :
  'a * 'b ->
  ((('b * 'c) * Lexer.token) Lexer.Stream.t -> 'd) ->
  (('b * 'c) * Lexer.token) Lexer.Stream.t -> 'd
val peek_in_ghost_range :
  ((int -> ('a * Lexer.token) option) * int ref *
   ('a * Lexer.token) option list ref -> 'b) ->
  (int -> ('a * Lexer.token) option) * int ref *
  ('a * Lexer.token) option list ref -> 'b
type spec_clause =
    NonghostCallersOnlyClause
  | FuncTypeClause of string * Ast.type_expr list * (Lexer.loc * string) list
  | RequiresClause of Ast.asn
  | EnsuresClause of Ast.asn
module Scala :
  sig
    val keywords : string list
    val parse_decl : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.decl
    val parse_method : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.meth
    val parse_paramlist :
      (Lexer.loc * Lexer.token) Lexer.Stream.t ->
      (Ast.type_expr * string) list
    val parse_param :
      (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.type_expr * string
    val parse_type_ann :
      (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.type_expr
    val parse_type :
      (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.type_expr
    val parse_targlist :
      (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.type_expr list
    val parse_contract :
      (Lexer.loc * Lexer.token) Lexer.Stream.t ->
      Ast.asn * Ast.asn * (Ast.type_expr * Ast.asn) list
    val parse_asn : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.asn
    val parse_primary_expr :
      (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_add_expr : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_add_expr_rest :
      Ast.expr -> (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_rel_expr : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_rel_expr_rest :
      Ast.expr -> (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_expr : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.expr
    val parse_stmt : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.stmt
  end
type modifier =
    StaticModifier
  | FinalModifier
  | AbstractModifier
  | VisibilityModifier of Ast.visibility
val parse_decls : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.decl list
val parse_package_name : ('a * Lexer.token) Lexer.Stream.t -> string
val parse_package :
  ((((string * string) * int * int) * ((string * string) * int * int)) *
   Lexer.token)
  Lexer.Stream.t ->
  (((string * string) * int * int) * ((string * string) * int * int)) *
  string
val parse_import_names :
  ('a * Lexer.token) Lexer.Stream.t -> string * string option
val parse_import_name :
  ('a * Lexer.token) Lexer.Stream.t -> string * string option
val parse_import0 : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.import
val parse_import : (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.import
val parse_package_decl :
  (Lexer.loc * Lexer.token) Lexer.Stream.t -> Ast.package
val parse_scala_file :
  string -> (Lexer.range_kind -> Lexer.loc -> unit) -> Ast.package
val parse_java_file :
  string ->
  (Lexer.range_kind -> Lexer.loc -> unit) ->
  (Lexer.srcpos * ((string * string) * int * int) -> 'a) -> Ast.package
type 'a parser_ = (Lexer.loc * Lexer.token) Lexer.Stream.t -> 'a
val parse_include_directives : bool ref -> (Lexer.loc * string) list parser_
val parse_c_file :
  string ->
  (Lexer.range_kind -> Lexer.loc -> unit) ->
  (Lexer.loc -> unit) -> bool -> (Lexer.loc * string) list * Ast.package list
val parse_header_file :
  string ->
  string ->
  (Lexer.range_kind -> Lexer.loc -> unit) ->
  (Lexer.loc -> unit) -> (Lexer.loc * string) list * Ast.package list
val read_file_lines : string -> string list
val file_loc :
  string -> ((string * string) * int * int) * ((string * string) * int * int)
val expand_macros : (string * string) list -> string -> string
val path_macros : (string * string) list
val expand_path : string -> string
val concat_if_relative : string -> string -> string
val parse_jarspec_file_core : string -> string list * string list
val parse_jarsrc_file_core :
  string -> string list * string list * string list
