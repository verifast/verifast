let (|>) x f = f x

let args = Sys.argv |> Array.to_list |> List.tl |> String.concat " "

let sh cmd =
  print_endline cmd;
  let result = Sys.command cmd in
  if result <> 0 then failwith (Printf.sprintf "Command failed with exit code %d" result)

let () =
  Sys.remove "build-helper-latest.ml";
  sh "svn export https://dnetcode.cs.kuleuven.be/svn/verifast/verifast/trunk/build-helper.ml build-helper-latest.ml";
  sh ("ocaml build-helper-latest.ml --caller=build.ml " ^ args)
