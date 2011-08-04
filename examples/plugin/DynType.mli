(** A type that can be extended dynamically with more constructors *)
type dyn

(** Creates a new constructor for type [dyn] and returns two functions: the constructor itself, and a match function. *)
val create_ctor: unit -> ('a -> dyn) * (dyn -> 'a option)