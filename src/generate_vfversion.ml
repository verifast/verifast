#load "unix.cma"

open Unix

let vfversion_contents = 
  let version =
    try
      getenv "VFVERSION"
    with Not_found -> "(working copy build)"
  in
  let now = gmtime (time ()) in
  let now_year = now.tm_year + 1900 in
  let now_month = now.tm_mon + 1 in
  let now_day = now.tm_mday in
  
  let release_date = Printf.sprintf "%04d-%02d-%02d" now_year now_month now_day in
  "let version = \"" ^ version ^ "\"\n"
  ^ "let release_date = \"" ^ release_date ^ "\"\n"
;;

(* Note: adds an extra "\n" at the end if it is not present. Assumes
 * the "newline" the Ocaml API talks about is "\n".
 *)
let file_get_contents filename =
  let f = open_in filename in
  let rec iter () =
    try
      let line = input_line f in
      line ^ "\n" ^ iter ()
    with
      End_of_file -> ""
  in
  iter ()
;;

let main () =
  let filename = "vfversion.ml" in
  let contents_shouldbe = vfversion_contents in

  (* Only write new file if the contents is really new,
   * otherwise the mtime changes and you end up unnecessarily
   * rebuilding all files depending on vfversion.ml
   *)
  let should_write =
    not (Sys.file_exists filename)
    or (file_get_contents filename) <> contents_shouldbe
  in

  if should_write then begin
    let f = open_out filename in
    let () = output_string f contents_shouldbe in
    close_out f
  end
;;

main ()
