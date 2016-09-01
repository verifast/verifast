external getpid: unit -> int32 = "caml_stopwatch_getpid"

(** Locks this process to processor 1.
  * This potentially improves the accuracy of timing results on multicore systems.
  * This module uses the RDTSC (read timestamp counter) instruction; these counters might not run in lockstep on the different processors of a system. *)
external lock_process_to_processor_1: unit -> unit = "caml_lock_process_to_processor_1"

external processor_ticks: unit -> int64 = "caml_stopwatch_processor_ticks"

(** The type of stopwatches. *)
type t = Obj.t

external create: unit -> t = "caml_stopwatch_create"
external start: t -> unit = "caml_stopwatch_start"
external stop: t -> unit = "caml_stopwatch_stop"
external ticks: t -> int64 = "caml_stopwatch_ticks"
