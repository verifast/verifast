type assert_result = Unknown | Unsat

type symbol_kind = Ctor of int | Fixpoint of int | Uninterp

class virtual ['symbol, 'termnode] context =
  object
    method virtual alloc_symbol: symbol_kind -> string -> 'symbol
    method virtual set_fpclauses: 'symbol -> ('termnode list -> 'termnode list -> 'termnode) array option -> unit
    method virtual get_termnode: 'symbol -> 'termnode list -> 'termnode
    method virtual pprint: 'termnode -> string
    method virtual reduce: unit
    method virtual value_eq: 'termnode -> 'termnode -> bool
    method virtual value_neq: 'termnode -> 'termnode -> bool
    method virtual assert_eq_and_reduce_terms: 'termnode -> 'termnode -> assert_result
    method virtual assert_neq_and_reduce_terms: 'termnode -> 'termnode -> assert_result
    method virtual push: unit
    method virtual pop: unit
  end
