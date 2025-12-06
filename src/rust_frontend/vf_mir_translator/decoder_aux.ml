module D = Vf_mir_decoder

let uint128_get (n : D.uint128) =
  let open Stdint.Uint128 in
  let h = n.h in
  let l = n.l in
  let r = of_uint64 h in
  let r = shift_left r 64 in
  let r = add r (of_uint64 l) in
  r
