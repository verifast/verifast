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
open General_ast

exception AnnotationTypeCheckerException of string

let debug_print m = Printf.printf "<annotation_type_checker> %s\n" m
let debug_print m = ()

class type ann_type_checker =
object
  method check_annotation : string -> t_frontend_communication -> unit
  method retrieve_annotations : unit -> (string, string) Hashtbl.t
end

class dummy_ann_type_checker () : ann_type_checker =
object (this)
  val annotations : (string, string) Hashtbl.t = Hashtbl.create 20
  method check_annotation a comm =
    let lines = Misc.split_string '\n' a in
    let loc = General_ast.string_of_loc (Ast_reader.parse_loc (Ast_reader.make_lexer Ast_reader.keywords (List.hd lines))) in
    let ann = String.concat "\n" (List.tl lines) in
    debug_print ("Adding annotation (@" ^ loc ^ "\n" ^ ann);
    Hashtbl.add annotations loc ann
  method retrieve_annotations _ = annotations
end

(*
let command_handle_type = "TYPE"

class vf_ann_type_checker () : ann_type_checker =
object (this)
  val annotations : (string, string) Hashtbl.t = Hashtbl.create 20
  method check_annotation a comm =   
    let delim = "_____________________________________________" in
    Printf.printf "%s\n" delim;
  
      (* do parsing and type checking of annotation m *)
      comm#send_command(command_handle_type ^ 
                                   command_separator ^ a);
      let (k, r) = comm#receive_response () in
      if (k <> SUCCESS) then
        raise (AnnotationTypeCheckerException ("Type checking of annotation failed!!!!!!!!!!!"))
      else
        Printf.printf "Type check response %s\n" r;
  
    Printf.printf "%s\n" delim
  method retrieve_annotations _ = annotations
end*)
