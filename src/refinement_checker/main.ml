open Refinement_checker

let original_path, verified_path =
  match Sys.argv with
  | [| _; original_path; verified_path |] -> (original_path, verified_path)
  | _ ->
      print_endline
        "Usage: refinement_checker <original_path> <verified_path>\n\n\
         Checks that each behavior of each function in the original path is \
         also exhibited by the corresponding function in the verified path";
      exit 1

let () = Perf.init_windows_error_mode ()
let rustc_args = []

let original_vf_mir = VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir rustc_args original_path
let verified_vf_mir = VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir rustc_args verified_path

(* Check, for each function body in original_vf_mir, that there is a matching function body in verified_vf_mir *)
let original_bodies = VfMirRd.VfMir.bodies_get_list original_vf_mir

let verified_bodies =
  VfMirRd.VfMir.bodies_get_list verified_vf_mir
  |> List.map (fun body -> (VfMirRd.Body.def_path_get body, body))

let () =
  original_bodies
  |> List.iter @@ fun body ->
     let def_path = VfMirRd.Body.def_path_get body in
     match List.assoc_opt def_path verified_bodies with
     | None ->
         error
           (Printf.sprintf "Function body %s not found in verified path"
              def_path)
     | Some verified_body ->
         check_body_refines_body def_path body verified_body

let () = Printf.printf "No refinement errors found\n"
