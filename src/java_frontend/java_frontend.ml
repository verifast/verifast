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

open Communication
open Ast_reader

exception JavaFrontendException of (General_ast.loc option * string)

let frontend_error l m =
  raise (JavaFrontendException (l, m))

let catch_exceptions f =
  try
    f ()
  with
  | Communication.CommunicationException (m) -> 
      frontend_error None ("Communucation Failure: " ^ m)
  | Ast_reader.AstReaderException(l, m) -> 
      frontend_error l m

type ast_option = string

let desugar : ast_option = "DESUGAR"
let bodyless_methods_own_trailing_annotations : ast_option = "EMPTY_METHODS"

let communication = 
  catch_exceptions get_communication_channel

(** @param ast_server_launch   command to launch the ast_server *)
let attach ast_server_launch = 
  catch_exceptions (fun _ -> communication#load(ast_server_launch))

let detach () =
  catch_exceptions (fun _ -> communication#unload())

(* method to send a FILE request with corresponding options and parse the response message *)
let ast_from_java_file_core f opts achecker =
  catch_exceptions (fun _ ->
    communication#send_command(command_handle_file ^ command_separator ^
                               f ^ command_separator ^ (String.concat command_separator opts));
    let kind = ref CALLBACK in
    let response = ref "" in
    let recieve _ =
      let (k, r) = communication#receive_response () in
      kind := k;
      response := r;
    in
    recieve ();
    while(!kind <> SUCCESS) do
      if (!kind <> CALLBACK) then
        frontend_error None 
          ("Callback failure: expected " ^ (string_of_response_kind CALLBACK) ^ 
           " message, but got " ^ (string_of_response_kind !kind) ^ " message");
      achecker#check_annotation !response communication;
      communication#send_command(command_continue);
      recieve ();
    done;
    Ast_reader.read_ast (!response)
  )

(* method to send a FILE request and parse the response message with the given options *)
let ast_from_java_file f opts achecker =
  catch_exceptions (fun _ -> ast_from_java_file_core f opts achecker)
