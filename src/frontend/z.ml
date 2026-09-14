(* Implemented using a string for now. TODO: Use Zarith. *)

(* Invariant: is a valid base-10 textual representation of an integer, with no leading zeros except for the number zero itself *)
type t = string

exception Overflow

let zero = "0"
let one = "1"
let minus_one = "-1"
let of_int: int -> t = string_of_int
let of_int32: int32 -> t = Int32.to_string
let of_int64: int64 -> t = Int64.to_string
let of_nativeint: nativeint -> t = Nativeint.to_string
let of_uint32: Stdint.Uint32.t -> t = Stdint.Uint32.to_string
let of_uint64: Stdint.Uint64.t -> t = Stdint.Uint64.to_string
let of_int128: Stdint.Int128.t -> t = Stdint.Int128.to_string
let of_uint128: Stdint.Uint128.t -> t = Stdint.Uint128.to_string
let of_big_int: Big_int.big_int -> t = Big_int.string_of_big_int
let to_int z = try int_of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_int32 z = try Int32.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_int64 z = try Int64.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_nativeint z = try Nativeint.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_uint32 z = try Stdint.Uint32.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_uint64 z = try Stdint.Uint64.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_int128 z = try Stdint.Int128.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_uint128 z = try Stdint.Uint128.of_string z with Failure _ -> raise Overflow
(** Raises an [Overflow] if the value does not fit. *)
let to_big_int z = Big_int.big_int_of_string z
let to_string z = z
