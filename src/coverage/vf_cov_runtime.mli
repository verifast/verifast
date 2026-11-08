(** [register_module ~file ~points] registers an instrumented module with its points.
    Each point is [(line, col, kind)] where kind is "fun", "case", "then", "else", "while", or "for".
    Returns the unique module ID. *)
val register_module : file:string -> points:(int * int * string) array -> int

(** [hit mod_id pt_id] increments the hit counter for point [pt_id] in module [mod_id]. *)
val hit : int -> int -> unit

(** [dump_stats ()] writes accumulated coverage statistics to a [.vfcov] file in
    [$VF_COVERAGE_DIR] if set and non-empty. *)
val dump_stats : unit -> unit

(** [get_registered_modules ()] returns all currently registered modules with their
    file name, points metadata array, and counters array. *)
val get_registered_modules : unit -> (string * (int * int * string) array * int array) list
