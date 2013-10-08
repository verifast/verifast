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

(* This file specifies the interface of the Java frontend.
   Using this interface a type checked AST can be retrieved 
   from a specific Java source file.
*)

(* Exception that indicates that an error occurred while generating
   an AST. If a location makes sense for the error a location is also
   specified. All functions in this file may raise a JavaFrontendException
*)
exception JavaFrontendException of (General_ast.loc option * string)

(* Load the AstServer: 
    @param1        command string to launch the AstServer  
    @return        ()
    @raise         JavaFrontendException If the AstServer could not be launched
*)
val attach : string -> unit

(*  Notify and unload the AstServer 
    @param1        ()
    @return        ()
    @raise         JavaFrontendException If the AstServer could not be stopped
*)
val detach : unit -> unit


(* possible options for generating an AST *)

  type ast_option
  
  (* Perform desugaring before generating AST,  
     this includes extraction of inner classes and 
     instantiation of generics. *)
  val desugar : ast_option

  (* Add the annotations following a interface method
     or an abstract method, to that method and not treat
     them as class level declarations. *)
  val bodyless_methods_own_trailing_annotations : ast_option

(* Create a desugared AST from the specified file
     @param1        path of the file to create a desugared AST from
     @param2        options options for creating the AST 
     @param3        annotation checker to parse and type check the encountered annotations while creating the AST
     @return        the AST generated from the specified file
     @raise         JavaFrontendException If the AstServer could not generated an AST from the speci
*)
val ast_from_java_file : string -> ast_option list -> Annotation_type_checker.ann_type_checker -> General_ast.package
