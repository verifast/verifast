(*

Copyright (C) 2013 KULeuven, Department of Computer Science, Gijs Vanspauwen
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

open Sys

open Java_frontend
open Annotation_type_checker
open Ast_writer

(* debug print *)
let debug_print x = 
  Printf.printf "<OCaml debug> main.ml - %s\n" x

(* main function *)
let _ =
  let arguments = List.tl (Array.to_list (Sys.argv)) in
  if (List.length arguments < 1) then begin
    let exec_name = List.hd (Array.to_list (Sys.argv)) in
    Printf.printf "\n%s\n%s\n\n" 
      "You should specify the location of the ast_server.jar file as the first argument: "
      ("Usage: " ^ exec_name  ^ " ast_server_location file1 file2 ... fileN");
    exit 1
  end;
  if (List.length arguments < 2) then begin
    Printf.printf "\n%s\n\n" "No files specied";
    exit 0
  end;
  let ast_server_url = List.hd arguments in
  let javas = List.tl arguments in
  Java_frontend.attatch ast_server_url;
  let asts = 
    try
      let achecker = new Annotation_type_checker.dummy_ann_type_checker () in
      List.map (fun x -> Java_frontend.ast_from_java_file x [ast_option_desugar] achecker) javas 
    with 
    | Java_frontend.JavaFrontendException(m) ->
        debug_print ("JavaFrontendException in main: \n" ^ m);
        Java_frontend.detatch ();
        exit 2
  in
  List.iter (fun x -> (Ast_writer.write_ast x)) asts;
  Java_frontend.detatch ();
  