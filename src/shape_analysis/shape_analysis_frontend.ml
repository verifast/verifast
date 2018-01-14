(**
 * Shape analyser frontend
 *
 * The frontend is the glue before the backend: it makes sure the file is
 * parsed to an AST, the relevant part of the AST is taken, and passes
 * this AST to the backend. The backend returns a list of changes (e.g.
 * insert an annotation at some position) to the frontend. The frontend
 * modifies the source file by applying these changes.
 *
 * Files are read but changes are not written to disk (the new contents is
 * passed as string). This makes it easier for the IDE to support undo.
 *)
 

open Shape_analysis_backend
open Parser (* for file_type *)
open Changelog
open Ast

exception ShapeAnalysisException of (loc * string);;

(**
 * The main function of the shape analyser frontend (see specs at top of
 * this file).
 * The contents is passed as a filename (instead of e.g. the real contents)
 * because the rest of VeriFast works like that.
 *)
let shape_analyse_frontend path include_paths define_macros position : string =
  let (_, ast_all) = parse_c_file path (fun _ _ -> ()) (fun _ -> ()) 0 include_paths define_macros true data_model_32bit in
  let ast_function =
    match ast_all with
    | [PackageDecl (loc, package_name, imports, declarations)] -> begin
        match declarations with
        | [Func _] as singleton_declaration -> singleton_declaration
        | _ -> raise (ShapeAnalysisException (dummy_loc, "currently only files consisting of one single function supported"))
      end
    | _ -> raise (ShapeAnalysisException (dummy_loc, "multiple package/module declarations not supported yet"))
  in
  let changes = shape_analyse_backend ast_function in
  let file_contents = "" (* TODO: read file to string.
                            Maybe you can reuse read_file_lines from parser.ml *) in
  changelog_apply file_contents changes
;;

