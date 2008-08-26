type assume_result = Unknown | Unsat

type symbol_kind = Ctor of int | Fixpoint of int | Uninterp

class virtual ['symbol, 'termnode] context =
  object
    method virtual alloc_symbol: int -> symbol_kind -> string -> 'symbol
    method virtual set_fpclauses: 'symbol -> int -> ('symbol * ('termnode list -> 'termnode list -> 'termnode)) list -> unit
    method virtual get_termnode: 'symbol -> 'termnode list -> 'termnode
    method virtual pprint: 'termnode -> string
    method virtual push: unit
    method virtual pop: unit
    method virtual assume_eq: 'termnode -> 'termnode -> assume_result
    method virtual assume_neq: 'termnode -> 'termnode -> assume_result
    method virtual query_eq: 'termnode -> 'termnode -> bool
    method virtual query_neq: 'termnode -> 'termnode -> bool
  end
