let () =
  let [| _; system |] = Sys.argv in
  let platform =
    match Sys.os_type with
      "Win32" -> "Windows"
    | _ ->
      match system with
        "macosx" -> "MacOS"
      | _ -> "Linux"
  in
  let chan = open_out "vfconfig.ml" in
  Printf.fprintf chan "let z3_present = false
let z3v4dot5_present = true
type platform = Windows | MacOS | Linux
let platform = %s
" platform;
  close_out chan
