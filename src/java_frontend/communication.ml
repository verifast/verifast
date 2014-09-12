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

open Ast_reader

exception CommunicationException of string

(* debug print *)
let debug_print x =
  Printf.printf "<OCaml debug> communication.ml - %s\n" x
let debug_print x = ()

(* ------------------------ *)
(* General stuff            *)
(* ------------------------ *)

(* commands *)
let command_separator                  = " "
let command_stop                       = "STOP"
let command_handle_files               = "FILES"
let command_type                       = "TYPE"
let file_separator                     = "//\\\\"
let command_continue                   = "CONTINUE"

(* responses *)
let response_success            = "SUCCESS"
let response_found_annotation   = "ANNOTATION"
let response_report_should_fail = "SHOULD_FAIL"
let response_failure            = "FAILURE"
let response_abort              = "ABORT"
let begin_of_message            = "++++++++++"
let end_of_message              = "----------"

type response_kind =
  | SUCCESS
  | ANNOTATION
  | SHOULD_FAIL
  
let string_of_response_kind k =
  match k with 
  | SUCCESS     -> response_success
  | ANNOTATION  -> response_found_annotation
  | SHOULD_FAIL -> response_report_should_fail

let responses = [response_success;
                 response_found_annotation;
                 response_report_should_fail;
                 response_failure;
                 response_abort]

(* ------------------------ *)
(* Communication Interface  *)
(* ------------------------ *)

class type virtual t_frontend_communication =
object
  (* expects a string represention of the command line 
     arguments passed to the the ASTServer  *)
  method load             : string -> unit
  method unload           : unit
  
  (* accepts a single line string command to send *)
  method send_command     : string -> unit
  (* returns a message possibly spanning multiple lines *)
  method receive_response : (response_kind * string list)
end

(* ----------------------------- *)
(* Communication Abstract Class  *)
(* ----------------------------- *)

class virtual abstract_communication =
object (this)
  val mutable virtual input : in_channel
  val mutable virtual output : out_channel
  method virtual generate_args : string
  method virtual ast_server_tag : string
  method virtual init_channels : unit
  
  val mutable attached = false
  val mutable ast_server_stdin = stdin
  val mutable ast_server_stdout = stdout
  
  (*val mutable thread  = Thread.self ()
  val mutable id_self = Thread.id (Thread.self ())*)
  
  method error m =
    raise (CommunicationException m)
  
  method load ast_server_launch =
    if (not attached) then begin
      let (i, o) = 
        Unix.open_process (ast_server_launch ^ " " ^ 
               this#ast_server_tag ^ " " ^ (this#generate_args)) 
      in
      ast_server_stdin <- i;
      ast_server_stdout <- o;
      this#init_channels;
      attached <- true
    end

  method unload =
    if (attached) then begin       
      (try
        this#send_command("STOP");
        let (kind, result) = this#receive_response in
        match kind with 
          SUCCESS ->
            if (result <> []) then
              let message =
                "Got a non-empty reply from ASTServer while expecting" ^
                " one \ncontents of the message : " ^
                (Misc.join_lines_never_fail result)
              in
              this#error message;
            let _ = Unix.close_process (ast_server_stdin, ast_server_stdout) in ()
        | _ -> this#error ("Got a callback from ASTServer while unloading");
      with
        _ -> this#error ("Unloading of ASTServer failed"));
      attached <- false
    end

  method send_message(message) =
    if (not attached) then
      this#error ("ASTServer is not attached");
    let m = begin_of_message ^ "\n" ^ message ^ "\n" ^ end_of_message ^ "\n" in
    output_string output m;
    flush output;
    debug_print ("send_message:\n" ^ message)

  method receive_message =
    if (not attached) then
      this#error ("ASTServer is not attached");
    let message = ref [] in
    let finished = ref false in
    while (not !finished) do
      try
        let line = input_line input in
        if (line = begin_of_message) then
          finished := true;
      with
        End_of_file -> ()
    done;
    finished := false;
    while (not !finished) do
      try
        let line = input_line input in
        if (line = end_of_message) then
          finished := true
        else
          message := line::!message
      with
        End_of_file -> ()
    done;
    List.rev !message
  
  method send_command(command) =
    if (String.contains command '\n') then
      this#error ("Presented command to send was not single line: " ^ command);
    this#send_message(command)

  method receive_response =
    let lines = this#receive_message in
    let message = Misc.join_lines_never_fail lines in
    debug_print ("receive_response got message: \n" ^ message);
    if (List.length lines < 1) then
      this#error ("Received a empty message from the ASTServer");
    let kind = List.hd lines in
    if not (List.mem kind responses) then
        this#error ("Received an incomprehensible message from the ASTServer: \n" ^ message);
    if kind = response_abort then begin
      this#unload;
      this#error ("ASTServer aborted while exetuting command: \n" ^ message)
    end;
    let parts = List.tl lines in
    if kind = response_failure then begin
      if (List.length parts < 2) then
        this#error ("Received an incomprehensible error message from the ASTServer: \n" ^ message);
      let l = Ast_reader.parse_line_with Ast_reader.parse_loc (List.hd parts) in
      raise (Ast_reader.AstReaderException(l, Misc.join_lines_never_fail (List.tl parts)))
    end;
    let kind =
      if kind = response_success then SUCCESS
      else if kind = response_found_annotation then ANNOTATION
      else if kind = response_report_should_fail then SHOULD_FAIL
      else (this#error ("ASTServer internal inconsistency"); SHOULD_FAIL)
    in
    (kind, parts)
end

(* ------------------------ *)
(* Socket implementation    *)
(* ------------------------ *)

class socket_communication =
object (this)
  inherit abstract_communication
  
  val initial_server_port = 4000
  val connection_attempts = 10
  val connection_timeout = 0.0001
  val mutable server_port = 4000
  
  val mutable input  = stdin
  val mutable output = stdout
  
  method ast_server_tag =
    "server"
    
  method generate_args =
    server_port <- initial_server_port;
    let finished = ref false in
    while(not !finished) do
      try begin
        let (ic, _) = Unix.open_connection (Unix.ADDR_INET((Unix.gethostbyname "localhost").Unix.h_addr_list.(0), server_port)) in
        try
          Unix.shutdown_connection ic;
        with
          Unix.Unix_error(_,_,_) -> ();
        server_port <- server_port + 1;
      end
      with e -> begin
        finished := true
      end
    done;
    string_of_int server_port
    
  method init_channels =
    let finished = ref false in
    while (not !finished) do
      let i = ref 0 in
      try begin
        let (ic, oc) = Unix.open_connection (Unix.ADDR_INET((Unix.gethostbyname "localhost").Unix.h_addr_list.(0), server_port)) in
        input <- ic;
        output <- oc;
        finished := true;
      end
      with e -> begin
        i := !i + 1;
        if (!i > connection_attempts) then
          this#error ("Failed to connect to ASTServer module of Java frontend, to many connection attempts");
        Thread.delay connection_timeout
      end
    done
end

(* ---------------------------------- *)
(* Standard streams implementation    *)
(* ---------------------------------- *)

class standard_streams_communication =
object (this)
  inherit abstract_communication
  
  val mutable input  = stdin
  val mutable output = stdout
  
  method ast_server_tag =
    "streams"
  
  method generate_args = ""
    
  method init_channels =
    input <- ast_server_stdin;
    output <- ast_server_stdout
end

(* let get_communication_channel _ = (new socket_communication : socket_communication :> t_frontend_communication) *)
let get_communication_channel _ = (new standard_streams_communication : standard_streams_communication :> t_frontend_communication)

