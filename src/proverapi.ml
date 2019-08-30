open Big_int
open Num

type assume_result = Unknown | Unsat

let string_of_assume_result = function
  | Unknown -> "unknown"
  | Unsat   -> "unsat"

(*

The ProverAPI logic has four sorts: bool, int, real, and inductive. 

Within sort 'inductive', so-called inductive subtypes with N constructors can
be defined by creating symbols with kind Ctor (CtorByOrdinal (subtype, k)) for
k = 0, ..., N-1. Also, primitive recursive functions ("fixpoints") can be
defined over these subtypes by creating symbols with kind Fixpoint (subtype, k)
where the function's k'th argument is the one on which structural recursion is
performed.

In the interpretation of the logic, different constructors of the same subtype
are disjoint, but nothing is assumed about constructors from different subtypes.
Indeed, it is consistent to imagine that the subtypes all overlap, and it is
sound to create a symbol and use it as a value of all subtypes. VeriFast exploits
this to support fixpoint default_value<t>(), declared as follows:

  fixpoint t default_value<t>();

Given that VeriFast erases type arguments, a single symbol default_value is
potentially used as a value of all subtypes.

*)

module InductiveSubtype : sig
  type t
  val alloc: unit -> t
  val lt: t -> t -> bool
  val to_int: t -> int
end = struct
  type t = int
  let next = ref 0
  let alloc () = let result = !next in incr next; result
  let lt x y = x < y
  let to_int x = x
end

type ctor_symbol = CtorByOrdinal of InductiveSubtype.t * int | NumberCtor of num
type symbol_kind = Ctor of ctor_symbol | Fixpoint of InductiveSubtype.t * int | Uninterp

class virtual ['typenode, 'symbol, 'termnode] context =
  object
    method virtual set_verbosity: int -> unit
    method virtual type_bool: 'typenode
    method virtual type_int: 'typenode
    method virtual type_real: 'typenode
    method virtual type_inductive: 'typenode
    method virtual mk_boxed_int: 'termnode -> 'termnode
    method virtual mk_unboxed_int: 'termnode -> 'termnode
    method virtual mk_boxed_real: 'termnode -> 'termnode
    method virtual mk_unboxed_real: 'termnode -> 'termnode
    method virtual mk_boxed_bool: 'termnode -> 'termnode
    method virtual mk_unboxed_bool: 'termnode -> 'termnode
    method virtual mk_symbol: string -> 'typenode list -> 'typenode -> symbol_kind -> 'symbol
    method virtual set_fpclauses: 'symbol -> int -> ('symbol * ('termnode list -> 'termnode list -> 'termnode)) list -> unit
    method virtual mk_app: 'symbol -> 'termnode list -> 'termnode
    method virtual mk_true: 'termnode
    method virtual mk_false: 'termnode
    method virtual mk_and: 'termnode -> 'termnode -> 'termnode
    method virtual mk_or: 'termnode -> 'termnode -> 'termnode
    method virtual mk_not: 'termnode -> 'termnode
    method virtual mk_ifthenelse: 'termnode -> 'termnode -> 'termnode -> 'termnode
    method virtual mk_iff: 'termnode -> 'termnode -> 'termnode
    method virtual mk_implies: 'termnode -> 'termnode -> 'termnode
    method virtual mk_eq: 'termnode -> 'termnode -> 'termnode
    method virtual mk_intlit: int -> 'termnode
    method virtual mk_intlit_of_string: string -> 'termnode
    method virtual mk_add: 'termnode -> 'termnode -> 'termnode
    method virtual mk_sub: 'termnode -> 'termnode -> 'termnode
    method virtual mk_mul: 'termnode -> 'termnode -> 'termnode
    (** C-style quotient: D == D / d * d + D % d and abs(D / d * d) <= abs(D) *)
    method virtual mk_div: 'termnode -> 'termnode -> 'termnode
    (** C-style modulo: D == D / d * d + D % d and abs(D / d * d) <= abs(D) *)
    method virtual mk_mod: 'termnode -> 'termnode -> 'termnode
    method virtual mk_lt: 'termnode -> 'termnode -> 'termnode
    method virtual mk_le: 'termnode -> 'termnode -> 'termnode
    method virtual mk_reallit: int -> 'termnode
    method virtual mk_reallit_of_num: num -> 'termnode
    method virtual mk_real_add: 'termnode -> 'termnode -> 'termnode
    method virtual mk_real_sub: 'termnode -> 'termnode -> 'termnode
    method virtual mk_real_mul: 'termnode -> 'termnode -> 'termnode
    method virtual mk_real_lt: 'termnode -> 'termnode -> 'termnode
    method virtual mk_real_le: 'termnode -> 'termnode -> 'termnode
    method virtual pprint: 'termnode -> string
    method virtual pprint_sort: 'typenode -> string
    method virtual pprint_sym: 'symbol -> string
    method virtual push: unit
    method virtual pop: unit
    method virtual assert_term: 'termnode -> unit
    method virtual assume: 'termnode -> assume_result
    method virtual query: 'termnode -> bool
    method virtual stats: string * (string * int64) list
    method virtual begin_formal: unit
    method virtual end_formal: unit
    method virtual mk_bound: int -> 'typenode -> 'termnode
    method virtual assume_forall: string (* description for diagnostic traces *) -> 'termnode list -> ('typenode) list -> 'termnode -> unit
    method virtual simplify: 'termnode -> 'termnode option
  end
