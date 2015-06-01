(*

Copyright (C) 2013 Katholieke Universiteit Leuven
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the <organization> nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

open General_ast
open Ast_reader
open Ast_writer
open Communication

exception JavaFrontendException of (General_ast.source_location * string)

let frontend_error l m =
  raise (JavaFrontendException (l, m))

let catch_exceptions f =
  try
    f ()
  with
  | Communication.CommunicationException (m) -> 
      frontend_error NoSource ("Communucation Failure: " ^ m)
  | Ast_reader.AstReaderException(l, m) -> 
      frontend_error l m

type ast_option = string

let desugar : ast_option = "DESUGAR"
let keep_assertions : ast_option = "KEEP_ASSERTIONS"
let keep_super_call_first : ast_option = "KEEP_SUPER_FIRST"
let bodyless_methods_own_trailing_annotations : ast_option = "EMPTY_METHODS"
let accept_spec_files : ast_option = "ACCEPT_SPEC_FILES"

let communication = 
  catch_exceptions get_communication_channel

let attached_status = ref false

(** @param ast_server_launch   command to launch the ast_server *)
let attach ast_server_launch = 
  catch_exceptions (fun _ -> communication#load(ast_server_launch));
  attached_status := true

let is_attached () = 
  !attached_status
  
let detach () =
  try communication#unload with _ -> ();
  attached_status := false
  
(* method to send a FILES request with corresponding options and parse the response message *)
let asts_from_java_files_core files cfiles opts report_should_fail annotaton_char_tag achecker =
  catch_exceptions (fun _ ->
    let files' = file_separator ^ (String.concat file_separator files) ^ file_separator in
    let cfiles' = file_separator ^ (String.concat file_separator cfiles) ^ file_separator in
    communication#send_command(command_handle_files ^ command_separator ^
                               annotaton_char_tag ^ command_separator ^
                               files' ^ command_separator ^
                               cfiles' ^ command_separator ^
                               (String.concat command_separator opts));
    let kind = ref ANNOTATION in
    let response = ref [] in
    let recieve _ =
      let (k, r) = communication#receive_response in
      kind := k;
      response := r;
    in
    recieve ();
    while(!kind <> SUCCESS) do
      if (!kind = ANNOTATION) then
        begin
          achecker#check_annotation (Misc.join_lines_never_fail !response) communication;
          communication#send_command(command_continue) 
        end
      else if (!kind = SHOULD_FAIL) then
        begin
          if (List.length !response <> 1) then
            frontend_error NoSource  
              ("Received an incomprehensible error message from the ASTServer: \n" ^ (String.concat "\n" !response));
          let l = Ast_reader.parse_line_with Ast_reader.parse_loc (List.hd !response) in
          report_should_fail l
        end
      else
        begin
          frontend_error NoSource 
            ("Callback failure: got a " ^ (string_of_response_kind !kind) ^ " message");
        end;
      recieve ()
    done;
    !response
  )

(* method to send a FILES request and parse the response message with the given options *)
let asts_from_java_files files ~context:cfiles opts report_should_fail annotaton_char_tag achecker =
  catch_exceptions (fun _ -> Ast_reader.read_asts (asts_from_java_files_core files cfiles opts report_should_fail annotaton_char_tag achecker))

let ast_from_java_file file opts report_should_fail annotaton_char_tag achecker =
  let result = asts_from_java_files [file] ~context:[] opts report_should_fail annotaton_char_tag achecker in
  if (List.length result != 1) then frontend_error dummy_loc "Single file did not result in single AST";
  List.hd result
