(** Returns the number of seconds since program startup.
  * On Windows, this function has better resolution (about 1 microsecond)
  * than Sys.time() (whose resolution is about 0.01 second). *)
  val time: unit -> float