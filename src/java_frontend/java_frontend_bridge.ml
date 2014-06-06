open Lexer
open Ast

open Ast_writer

let load _ =
  let launch = 
    try Sys.getenv "VERIFAST_JAVA_AST_SERVER"  
    with Not_found ->
      let ast_server_filename = "ast_server-1d80e62.jar" in
      let error_message =
        "\nYou specified the option -javac to use the STANCE Java frontend. " ^
        Printf.sprintf "However, to use the STANCE Java frontend, you need to retrieve the file %s from: \n" ast_server_filename ^
            "\t https://bitbucket.org/gijsv/stance-java-frontend \n" ^
        "Then you must set the environment variable VERIFAST_JAVA_AST_SERVER as follows: \n" ^
            Printf.sprintf "\t export VERIFAST_JAVA_AST_SERVER=\"java -jar path/to/%s\" \n" ast_server_filename
      in
      Printf.printf "%s" error_message;
      failwith error_message
  in
  Java_frontend.attach(launch)

let unload _ =
  Java_frontend.detach()

let parse_java_files_with_frontend (paths: string list) (context: string list) (reportRange: range_kind -> loc -> unit) reportShouldFail: package list =
(*   Printf.printf "\n\n%s\n%s\n%s\n" "----------------------------" "parse_java_files_with_frontend" "----------------------------"; *)
  let (rt_paths, paths) =
    List.partition (fun p -> Filename.dirname p = Util.rtdir) paths
  in
  let context = List.filter (fun x -> not (List.mem ((Filename.chop_extension x) ^ ".javaspec") paths)) context in
  let context = List.filter (fun x -> not (List.mem ((Filename.chop_extension x) ^ ".java") paths)) context in
(*   List.iter (fun x -> Printf.printf "rt_paths %s\n" x) rt_paths; *)
(*   List.iter (fun x -> Printf.printf "paths    %s\n" x) paths; *)
(*   List.iter (fun x -> Printf.printf "context  %s\n" x) context;   *)
  let result =
    match paths with
    | [] -> []
    | _ ->
      if not (Java_frontend.is_attached ()) then load();
        let ann_checker = new Annotation_type_checker.dummy_ann_type_checker () in
        let packages = 
          try
            let options = 
              [Java_frontend.desugar; 
              Java_frontend.keep_assertions;
              Java_frontend.keep_super_call_first;
              Java_frontend.bodyless_methods_own_trailing_annotations;
              Java_frontend.accept_spec_files]
            in
            Java_frontend.asts_from_java_files paths ~context:context options ann_checker
          with
            Java_frontend.JavaFrontendException(l, m) -> 
              let message = 
                String.concat " |" (Misc.split_string '\n' m)
              in
              match l with
              | General_ast.NoSource -> raise (Parser.CompilationError message)
              | _ -> raise (Lexer.ParseException(Ast_translator.translate_location l, message))
        in
        let annotations = ann_checker#retrieve_annotations () in
        Ast_translator.translate_asts packages annotations
   in
   (List.map (fun x -> Parser.parse_java_file_old x reportRange reportShouldFail) rt_paths) @ result 

let previous_context = ref []

let parse_java_files (paths: string list) (jars: string list) (reportRange: range_kind -> loc -> unit) reportShouldFail use_java_frontend: package list =
  if use_java_frontend then begin
    let context =
      let rec recurse_specs javas jars =
        match jars with
        | j::rest ->
            let jar = j ^ "src" in
(*             Printf.printf "Looking at jarspec file %s\n" jar; *)
            let (jars, specs, _) = Parser.parse_jarsrc_file_core jar in
(*             List.iter (fun p -> Printf.printf "Found jarsrc --------> %s\n" p) jars; *)
(*             List.iter (fun p -> Printf.printf "Found spec   --------> %s\n" p) specs; *)
            let path_dir = Filename.dirname jar in
            let jars = (List.map (Util.concat path_dir) jars) in
            let specs = (List.map (Util.concat path_dir) specs) in
(*             List.iter (fun p -> Printf.printf "Selected jarsrc --------> %s\n" p) jars; *)
(*             List.iter (fun p -> Printf.printf "Selected spec   --------> %s\n" p) specs; *)
            let check_dup l =
              match l with 
              | [] -> false
              | x::rest -> List.mem x rest
            in
            if check_dup jars then
              raise (ParseException (dummy_loc, "Include cycle in jarspec files"));
            recurse_specs (specs @ javas) (jars @ rest)
        | [] -> List.map (fun x -> x) javas
      in
      let recursive_context = recurse_specs [] jars in
      let recursive_context = List.filter (fun p -> not (List.mem ((Filename.chop_extension p) ^ ".java") paths)) recursive_context in
      let recursive_context = List.filter (fun p -> not (List.mem p paths)) recursive_context in
      if !previous_context = [] then previous_context := recursive_context;
      recursive_context
    in
    let context = if context = [] then !previous_context else context in
    parse_java_files_with_frontend paths context reportRange reportShouldFail
  end
  else
    List.map (fun x -> Parser.parse_java_file_old x reportRange reportShouldFail) paths

