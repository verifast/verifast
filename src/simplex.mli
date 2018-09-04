type result = Sat | Unsat

type 'tag unknown

val print_unknown: 'tag unknown -> string
val unknown_tag: 'tag unknown -> 'tag option

type 'tag simplex0 = <
  register_listeners:
    ('tag unknown -> 'tag unknown -> unit) ->
    ('tag unknown -> Num.num -> unit) ->
    unit;
  push: unit;
  pop: unit;
  alloc_unknown: string -> 'tag -> 'tag unknown;
  assert_ge: Num.num -> (Num.num * 'tag unknown) list -> result;
  assert_eq: Num.num -> (Num.num * 'tag unknown) list -> result;
  assert_neq: Num.num -> (Num.num * 'tag unknown) list -> result;
  get_ticks: int64;
  print: string
>

val new_simplex: unit -> 'tag simplex0