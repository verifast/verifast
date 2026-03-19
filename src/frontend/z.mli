(**
   Integers.
 *)

type t

exception Overflow

val zero: t
val one: t
val minus_one: t
val of_int: int -> t
val of_int32: int32 -> t
val of_int64: int64 -> t
val of_nativeint: nativeint -> t
val of_uint32: Stdint.Uint32.t -> t
val of_uint64: Stdint.Uint64.t -> t
val of_int128: Stdint.Int128.t -> t
val of_uint128: Stdint.Uint128.t -> t
val of_big_int: Big_int.big_int -> t
val to_int: t -> int
(** Raises an [Overflow] if the value does not fit. *)
val to_int32: t -> int32
(** Raises an [Overflow] if the value does not fit. *)
val to_int64: t -> int64
(** Raises an [Overflow] if the value does not fit. *)
val to_uint32: t -> Stdint.Uint32.t
(** Raises an [Overflow] if the value does not fit. *)
val to_uint64: t -> Stdint.Uint64.t
(** Raises an [Overflow] if the value does not fit. *)
val to_int128: t -> Stdint.Int128.t
(** Raises an [Overflow] if the value does not fit. *)
val to_uint128: t -> Stdint.Uint128.t
(** Raises an [Overflow] if the value does not fit. *)
val to_nativeint: t -> nativeint
(** Raises an [Overflow] if the value does not fit. *)
val to_big_int: t -> Big_int.big_int
val to_string: t -> string
