type assume_result = Unknown | Unsat

type symbol_kind = Ctor of int | Fixpoint of int | Uninterp

class virtual ['typenode, 'symbol, 'termnode] context =
  object
    method virtual type_bool: 'typenode
    method virtual type_int: 'typenode
    method virtual type_inductive: 'typenode
    method virtual mk_symbol: string -> 'typenode list -> 'typenode -> symbol_kind -> 'symbol
    method virtual set_fpclauses: 'symbol -> int -> ('symbol * ('termnode list -> 'termnode list -> 'termnode)) list -> unit
    method virtual mk_app: 'symbol -> 'termnode list -> 'termnode
    method virtual mk_true: 'termnode
    method virtual mk_false: 'termnode
    method virtual mk_and: 'termnode -> 'termnode -> 'termnode
    method virtual mk_or: 'termnode -> 'termnode -> 'termnode
    method virtual mk_not: 'termnode -> 'termnode
    method virtual mk_ifthenelse: 'termnode -> 'termnode -> 'termnode -> 'termnode
    method virtual mk_eq: 'termnode -> 'termnode -> 'termnode
    method virtual mk_intlit: int -> 'termnode
    method virtual mk_add: 'termnode -> 'termnode -> 'termnode
    method virtual mk_sub: 'termnode -> 'termnode -> 'termnode
    method virtual mk_lt: 'termnode -> 'termnode -> 'termnode
    method virtual mk_le: 'termnode -> 'termnode -> 'termnode
    method virtual pprint: 'termnode -> string
    method virtual push: unit
    method virtual pop: unit
    method virtual assume: 'termnode -> assume_result
    method virtual query: 'termnode -> bool
  end
