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

(* All functions in this file may raise JavaFrontendExceptions 
    arg1: error message
*)
exception JavaFrontendException of string

(* load the AstServer jar-file 
     arg1:   path to the ast_server.jar file
     result: _
*)
val attatch : string -> unit

(* notify and unload the AstServer 
     arg1:   _
     result: _
*)
val detatch : unit -> unit

(* possoble options for generating an ast *)
  (* Perform desugaring before generating ast,  
     this includes extraction of inner classes and 
     instantiation of generics. *)
  val ast_option_desugar : string
  (* Add the annotations following a interface method
     or an abstract method, to that method and not treat
     them as class level declarations. *)
  val ast_option_empty_methods : string

(* Create a desugared ast from the specified file
     arg1:   path of the file to create a desugared ast from
     arg2:   options for creating the ast 
     arg3:   annotation checker to parse and type check the encountered annotations while creating the ast
     result: the ast generated from the specified file
*)
val ast_from_java_file : string -> string list -> Annotation_type_checker.ann_type_checker -> General_ast.package
