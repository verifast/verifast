module R = Reader.R

module Make (Args : Sig.CXX_TRANSLATOR_ARGS) : Sig.Cxx_Ast_Translator = struct
  (*
     Maps unique identifiers - integers - to filenames.
     Every source location from Clang is passed as {i (int, int, int)} where
     the first integer represents the file. This map is used to retrieve the filename.
  *)
  let files_table : (int, string) Hashtbl.t = Hashtbl.create 8
  let get_fd_path = Hashtbl.find files_table

  module Node_translator = Node_translator.Make (struct
    include Args

    let path_of_int = get_fd_path
  end)

  module AP = Node_translator.Annotation_parser
  module Decl_translator = Decl_translator.Make (Node_translator)

  let int_rank, long_rank, ptr_rank =
    Parser.decompose_data_model Args.data_model_opt

  (**
    [invoke_exporter path allow_expansions] runs the C++ AST exporter. This tool visits each node
    in the C++ AST and serializes it. It also checks if every macro expansion is context free. 
    [allow_expansions] is a list of macros that should be allowed to expand, even
    if they depend on the context where they are included. 
    
    Returns ({i in_channel}, {i out_channel}, {i error_channel}), which should be closed afterwards.
    The serialized AST will be transmitted through {i in_channel} in case of success. Otherwise an error
    is transmitted through {i error_channel}. {i out_channel} should not be used.

    In case of success, the exporter first transmits a message {i SerResult.Ok} through {i in_channel} 
    to report that the compilation, context free macro expansion check, and AST serialization were successful.
    The next message that is transmitted through {i in_channel} represents the serialized C++ AST.

    Otherwise a message {i SerResult.Error} is transmitted through {i error_channel}
    if any error occurred during compilation, context free macro expansion checking, or AST serialization.
    This error message contains an explanation why the C++ AST exporter produced an error.
  *)
  let invoke_exporter (file : string) (allow_expansions : string list) =
    let bin_dir = Filename.dirname Sys.executable_name in
    let frontend_macro = "__VF_CXX_CLANG_FRONTEND__" in
    let allow_expansions = frontend_macro :: allow_expansions in
    (*
       -allow_macro_expansion=<expansions>   Don't check context-free expasions for <expansions>
       -x<language>                          Treat input files as having type <language>
       -I<dir>                               Include dir
       -D<macros>                            Define macros <macros>
    *)
    let cmd =
      Printf.sprintf
        "%s/vf-cxx-ast-exporter %s -allow_macro_expansion=%s -- -x%s \
         -std=c++17 -I%s -D%s %s"
        bin_dir file
        (String.concat "," allow_expansions)
        (match Args.dialect_opt with Some Cxx -> "c++" | _ -> "c")
        bin_dir frontend_macro
        (Args.include_paths |> List.map (fun s -> "-I" ^ s) |> String.concat " ")
    in
    let inchan, outchan, errchan = Unix.open_process_full cmd [||] in
    (inchan, outchan, errchan)

  (**
    [subs_ast_inc_channel pipe] creates a read context to dezerialize cap'n proto messages from the given
    [pipe]. This read context can be used to read multiple cap'n proto messages.
  *)
  let stubs_ast_in_channel pipe =
    Capnp_unix.IO.create_read_context_for_channel ~compression:`None pipe

  (**
    [read_capn_message read_context] reads {e one} cap'n proto message from [read_context].
  *)
  let read_capnp_message read_context =
    Capnp_unix.IO.ReadContext.read_message read_context

  (********************)
  (* translation unit *)
  (********************)

  let transl_includes (decls_map : (int * R.Node.t Capnp_util.capnp_arr) list)
      (includes : R.Include.t list) : Sig.header_type list =
    let active_headers = ref [] in
    let test_include_cycle l path =
      if List.mem path !active_headers then
        raise
          (Lexer.ParseException
             (l, "Include cycles (even with header guards) are not supported"))
    in
    let add_active_header path = active_headers := path :: !active_headers in
    let remove_active_header path =
      active_headers := List.filter (fun h -> h <> path) !active_headers
    in
    let transl_decls fd =
      List.assoc fd decls_map
      |> Capnp_util.arr_map Decl_translator.translate
      |> List.flatten
    in
    let open R.Include in
    let rec transl_includes_rec path incls header_names all_includes_done_paths
        =
      match incls with
      | [] -> ([], header_names)
      | h :: tl -> (
          match get h with
          | RealInclude incl ->
              let headers, header_name =
                transl_real_include_rec incl all_includes_done_paths
              in
              let other_headers, other_header_names =
                transl_includes_rec path tl
                  (header_name :: header_names)
                  (header_name :: all_includes_done_paths)
              in
              (List.append headers other_headers, other_header_names)
          | GhostInclude incl ->
              let ann = Node_translator.map_annotation incl in
              let included_files_ref = ref all_includes_done_paths in
              let ghost_headers, ghost_header_names =
                AP.parse_include_directives path ann active_headers
                  included_files_ref
              in
              let other_headers, other_header_names =
                transl_includes_rec path tl
                  (List.append ghost_header_names header_names)
                  !included_files_ref
              in
              (List.append ghost_headers other_headers, other_header_names))
    and transl_real_include_rec incl all_includes_done_paths =
      let open RealInclude in
      let file_name = file_name_get incl in
      let path = Util.abs_path file_name in
      let fd = fd_get incl in
      let loc = loc_get incl |> Node_translator.translate_loc in
      if List.mem path all_includes_done_paths then
        let () = test_include_cycle loc path in
        ([], path)
      else
        let incl_kind =
          if is_angled_get incl then Lexer.AngleBracketInclude
          else Lexer.DoubleQuoteInclude
        in
        let includes = includes_get_list incl in
        let () = add_active_header path in
        let headers, header_names =
          transl_includes_rec path includes [] (path :: all_includes_done_paths)
        in
        let () = remove_active_header path in
        let decls = transl_decls fd in
        let ps = [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ] in
        ( List.append headers
            [ (loc, (incl_kind, file_name, path), header_names, ps) ],
          path )
    in
    let headers, _ = transl_includes_rec Args.path includes [] [] in
    headers

  (**
    [update_file_mapping file] updates the mapping from [file]'s file descriptor to its name and returns the mapping.
  *)
  let update_file_mapping (file : R.File.t) : int * string =
    let open R.File in
    let fd = fd_get file in
    let name = path_get file in
    Hashtbl.replace files_table fd name;
    (fd, name)

  let transl_files (files : R.File.t Capnp_util.capnp_arr) :
      (int * R.Node.t Capnp_util.capnp_arr) list =
    Hashtbl.clear files_table;
    let transl_file file =
      let open R.File in
      let fd, _ = update_file_mapping file in
      let decls = decls_get file in
      (fd, decls)
    in
    files |> Capnp_util.arr_map transl_file

  let transl_vf_err (err : R.VfError.t) : 'a =
    let transl_err (err : R.Err.t) : 'a =
      let open R.Err in
      let loc = Node_translator.translate_loc @@ loc_get err in
      let reason = reason_get err in
      Error.error loc reason
    in
    let open R.VfError in
    let tu = tu_get err in
    (* we need the file mapping to translate the location of errors *)
    let () =
      R.TU.files_get tu
      |> Capnp_util.arr_iter (fun f -> update_file_mapping f |> ignore)
    in
    let errors = errors_get err in
    errors |> Capnp_util.arr_iter transl_err

  let transl_tu (tu : R.TU.t) : Sig.header_type list * Ast.decl list =
    let open R.TU in
    let decls_table = files_get tu |> transl_files in
    let includes = includes_get_list tu |> transl_includes decls_table in
    let main_fd = main_fd_get tu in
    let main_decls =
      List.assoc main_fd decls_table
      |> Capnp_util.arr_map Decl_translator.translate
      |> List.flatten
    in
    let () =
      fail_directives_get tu
      |> Capnp_util.arr_map Node_translator.map_annotation
      |> List.iter @@ fun (l, s) -> Args.report_should_fail s l
    in
    (includes, main_decls)

  let parse_cxx_file () : Sig.header_type list * Ast.package list =
    (* TODO: pass macros that are whitelisted *)
    let type_macros pref =
      [ 8; 16; 32; 64 ]
      |> List.map @@ fun n -> Printf.sprintf "__%s%u_TYPE__" pref n
    in
    let enable_types = type_macros "INT" @ type_macros "UINT" in
    let inchan, outchan, errchan = invoke_exporter Args.path enable_types in
    let close_channels () =
      let _ = Unix.close_process_full (inchan, outchan, errchan) in
      ()
    in
    let on_error () =
      match Util.input_fully errchan with
      | "" ->
          failwith
            "the Cxx frontend was unable to deserialize the received message."
      | s -> failwith @@ "Cxx AST exporter error:\n" ^ s
    in
    let in_channel = stubs_ast_in_channel inchan in
    Util.do_finally
      (fun () ->
        match read_capnp_message in_channel with
        | None -> on_error ()
        | Some res -> (
            match res |> R.SerResult.of_message |> R.SerResult.get with
            | R.SerResult.Undefined _ -> on_error ()
            | R.SerResult.Ok tu ->
                let headers, decls = transl_tu tu in
                (headers, [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ])
            | R.SerResult.ClangError -> on_error ()
            | R.SerResult.VfError err ->
                let () = transl_vf_err err in
                on_error ()))
      (fun () -> close_channels ())
end
