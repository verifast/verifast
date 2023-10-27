external query_performance_counter: unit -> int64 = "caml_query_performance_counter"
external query_performance_frequency: unit -> int64 = "caml_query_performance_frequency"

let counter0_int64 = query_performance_counter ()

let freq_int64 = query_performance_frequency ()
let freq_float = Int64.to_float freq_int64
let count_length = 1.0 /. freq_float

let seconds_since_startup () =
  Int64.to_float (query_performance_counter ()) *. count_length

let time () =
  Int64.to_float (Int64.sub (query_performance_counter ()) counter0_int64) *. count_length