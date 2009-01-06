#load "unix.cma"

open Unix

let version =
  try
    getenv "VFVERSION"
  with Not_found -> "(working copy build)"

let now = gmtime (time ())
let now_year = now.tm_year + 1900
let now_month = now.tm_mon + 1
let now_day = now.tm_mday

let release_date = Printf.sprintf "%04d-%02d-%02d" now_year now_month now_day

let f = open_out "vfversion.ml"

let _ =
  output_string f ("let version = \"" ^ version ^ "\"\n")
let _ =
  output_string f ("let release_date = \"" ^ release_date ^ "\"\n")
let _ =
  close_out f
