open Ast
open Lexer

open Ast_writer

let load _ =
  try
    let launch = 
      try Sys.getenv "VERIFAST_JAVA_AST_SERVER"  
      with Not_found ->
        let ast_server_filename = "ast_server_" ^ Misc.release_version ^ ".jar" in
        let error_message =
          "\nYou specified the option -javac to use the STANCE Java frontend. " ^
          Printf.sprintf "However, to use the STANCE Java frontend, you need to retrieve the file %s from: \n" ast_server_filename ^
              "\t https://doi.org/10.5281/zenodo.3373250 \n" ^
          "Then you must set the environment variable VERIFAST_JAVA_AST_SERVER as follows: \n" ^
              Printf.sprintf "\t export VERIFAST_JAVA_AST_SERVER=\"java -jar path/to/%s\" \n" ast_server_filename
        in
        Printf.printf "%s" error_message;
        failwith error_message
    in
    Java_frontend.attach(launch)
  with
    Java_frontend.JavaFrontendException(_, msg) -> raise (Parser.CompilationError msg)

let unload _ =
  Java_frontend.detach()

let found_java_spec_files = ref []

let build_context paths jars = 
  let rec recurse_specs javaspecs jars =
    match jars with
    | j::rest ->
        let jar = (Filename.chop_extension j) ^ ".jarspec" in
        let (jars, specs) = Parser.parse_jarspec_file_core jar in
        let path_dir = Filename.dirname jar in
        let jars = (List.map (Util.concat path_dir) jars) in
        let specs = (List.map (Util.concat path_dir) specs) in
        let check_dup l =
          match l with 
          | [] -> false
          | x::rest -> List.mem x rest
        in
        if check_dup jars then
          raise (ParseException (dummy_loc, "Include cycle in jarspec files"));
        recurse_specs (specs @ javaspecs) (jars @ rest)
    | [] -> javaspecs
  in
  recurse_specs [] jars

let rec parse_java_files_with_frontend (paths: string list) (jars: string list) (reportRange: range_kind -> loc0 -> unit) reportShouldFail verbose enforceAnnotations: package list =
  let context_new = build_context paths jars in
  found_java_spec_files := Util.list_remove_dups (!found_java_spec_files @ context_new);
  let context_for_paths = List.filter (fun x -> not (List.mem ((Filename.chop_extension x) ^ ".javaspec") paths)) !found_java_spec_files in
  let context_for_paths = List.filter (fun x -> not (List.mem ((Filename.chop_extension x) ^ ".java") paths)) context_for_paths in
  let parse paths =
    try
      if not (Java_frontend.is_attached ()) then load();
      let ann_checker = new Annotation_type_checker.dummy_ann_type_checker () in
      let fe_options =
        [Java_frontend.desugar; 
        Java_frontend.keep_assertions;
        Java_frontend.keep_super_call_first;
        Java_frontend.bodyless_methods_own_trailing_annotations;
        Java_frontend.accept_spec_files]
      in
      let reportShouldFail' l =
        let Lexed l = Ast_translator.translate_location l in
        reportShouldFail l
      in
      let packages = 
        Java_frontend.asts_from_java_files paths ~context:context_for_paths fe_options reportShouldFail' "verifast_annotation_char" ann_checker
      in
      let annotations = ann_checker#retrieve_annotations () in
      Ast_translator.translate_asts packages annotations reportRange reportShouldFail enforceAnnotations
    with
      Java_frontend.JavaFrontendException(l, m) -> 
        let message = 
          String.concat " |" (Misc.split_string '\n' m)
        in
        match l with
        | General_ast.NoSource -> raise (Parser.CompilationError message)
        | _ -> raise (Parser.StaticError(Ast_translator.translate_location l, message, None))
  in
  match paths with
    | [] -> []
    | _ -> (parse paths)

let parse_java_files (paths: string list) (jars: string list) (reportRange: range_kind -> loc0 -> unit) reportShouldFail verbose enforceAnnotations useJavaFrontend: package list =
  if useJavaFrontend then
    parse_java_files_with_frontend paths jars reportRange reportShouldFail verbose enforceAnnotations
  else
    List.map (fun x -> Parser.parse_java_file_old x reportRange reportShouldFail verbose enforceAnnotations) paths 

