let sh cmd =
  print_endline cmd;
  let result = Sys.command cmd in
  if result <> 0 then failwith (Printf.sprintf "Command failed with exit code %d" result)

let () =
  sh "svn export https://aramis.cs.kuleuven.be/svn/verifast/verifast/trunk/build-helper.ml build-helper-latest.ml";
  sh "ocaml build-helper-latest.ml --caller=build.ml"
