type t
val of_string : string -> t
val of_mangled : ?name:string -> string -> t
val id : t -> string
val name : t -> string
val map : (string -> string) -> t -> t
