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

exception CommunicationException of string

(* ------------------------ *)
(* General stuff            *)
(* ------------------------ *)

(* commands *)
let command_separator                  = " "
let command_stop                       = "STOP"
let command_handle_file                = "FILE"
let command_continue                   = "CONTINUE"

(* responses *)
let response_success  = "SUCCESS"
let response_callback = "CALLBACK"
let response_failure  = "FAILURE"
let response_abort    = "ABORT"
let begin_of_message  = "++++++++++"
let end_of_message    = "----------"

type response_kind =
  | SUCCESS
  | CALLBACK
  
let string_of_response_kind k =
  match k with 
  | SUCCESS -> response_success
  | CALLBACK -> response_callback

let responses = [response_success;
                 response_callback;
                 response_failure;
                 response_abort]

(* ------------------------ *)
(* Communication Interface  *)
(* ------------------------ *)

(** 
 -interface for communication with the ASTServer (i.e. java part of java frontend)
 -different implentations possible but implemenation must correspond to the one used in Java part 
 
 -currently only one implentation using sockets: socket_communication
 -SOLUTION1 Use stdin en stdout
 -SOLUTION2 Replace sockets by communication via communicating functions send and recieve:
            Java -> JNI -> C -> OCaml 
            (was not feasable for entire interface, but is for two simple functions)
  
  -to change the implementation write your own instance of a t_frontend_communication and 
   modify the function get_communication_channel in the bottom of this file
*)

class type t_frontend_communication =
object
  (* expects a string representing of the command to launch the ASTServer  *)
  method load             : string -> unit
  method unload           : unit -> unit
  
  (* accepts a single line string command to send *)
  method send_command     : string -> unit
  (* returns a message possibly spanning multiple lines *)
  method receive_response : unit -> (response_kind * string)
end

(* debug print *)
let debug_print x = ()
(*   Printf.printf "<OCaml debug> communication.ml - %s\n" x *)

(* ------------------------ *)
(* Socket implementation    *)
(* ------------------------ *)

class socket_communication () : t_frontend_communication=
object (this)
  val mutable thread  = Thread.self ()
  val mutable id_self = Thread.id (Thread.self ())
  val mutable in_channel  = stdin
  val mutable out_channel = stdout
  
  val initial_server_port = 4000
  val connection_attempts = 10
  val connection_timeout = 0.0001
  
  method private error m =
    raise (CommunicationException m)

  method load ast_server_launch =
    if (Thread.id thread = id_self) then
      try begin
        let finished = ref false in
        let server_port = ref initial_server_port in
        (* 
          first find a port that is still open and use that port
           as command line arg to ASTserver, in the meantime this 
           port could be occupied, but this situation is ignored (FOR NOW!)
           TODO: -let server choose port and pass port through stdout
                 -run ast_server_launch in simple separate process (in stead off thread + process)
        *)
        while(not !finished) do
          try begin
            let (ic, _) = Unix.open_connection (Unix.ADDR_INET((Unix.gethostbyname "localhost").Unix.h_addr_list.(0), !server_port)) in
            try
              Unix.shutdown_connection ic;
            with
              Unix.Unix_error(_,_,_) -> ();
            server_port := !server_port + 1;
          end
          with e -> begin
            finished := true
          end
        done;
        thread <- Thread.create (fun _ -> 
          Sys.command(ast_server_launch ^ " " ^ (string_of_int !server_port))) ();
        finished := false;
        while (not !finished) do
          let i = ref 0 in
          try begin
            let (ic, oc) = Unix.open_connection (Unix.ADDR_INET((Unix.gethostbyname "localhost").Unix.h_addr_list.(0), !server_port)) in
            in_channel <- ic;
            out_channel <- oc;
            finished := true;
          end
          with e -> begin
            i := !i + 1;
            if (!i > connection_attempts) then
              this#error ("Failed to connect to ASTServer ( command " ^ ast_server_launch ^ ") module of Java frontend, to many connection attempts");
            Thread.delay connection_timeout
          end
        done
      end
      with Unix.Unix_error(_, s1, s2) -> begin
        this#error ("Failed to connect to ASTServer ( command " ^ ast_server_launch ^ ") module of Java frontend")
      end

  method unload() =
    if (Thread.id thread <> id_self) then begin       
      (try
        this#send_command("STOP");
        let (kind, result) = this#receive_response() in
        match kind with 
          SUCCESS ->
            if (result <> "") then
              this#error ("Got a non-empty reply from ASTServer while expecting one \ncontents of the message : " ^ result);
            Unix.shutdown_connection in_channel;
        | CALLBACK -> this#error ("Got a callback from ASTServer while unloading");
      with
        _ -> ());
      Thread.join thread;
      thread <- Thread.self();
    end

  method private send_message(message) =
    if (Thread.id thread = id_self) then
      this#error ("ASTServer is not attached");
    let m = begin_of_message ^ "\n" ^ message ^ "\n" ^ end_of_message ^ "\n" in
    output_string out_channel m;
    flush out_channel;
    debug_print ("send_message:\n" ^ message)

  method private receive_message() =
    if (Thread.id thread = id_self) then
      this#error ("ASTServer is not attached");
    let message = ref [] in
    let finished = ref false in
    while (not !finished) do
      try
        let line = input_line in_channel in
        if (line = begin_of_message) then
          finished := true;
      with
        End_of_file -> ()
    done;
    finished := false;
    while (not !finished) do
      try
        let line = input_line in_channel in
        if (line = end_of_message) then
          finished := true
        else
          message := line::!message
      with
        End_of_file -> ()
    done;
    debug_print ("receive_message: \n" ^ (String.concat "\n" (List.rev !message)));
    List.rev !message
  
   method private send_command(command) =
    if (String.contains command '\n') then
      this#error ("Presented command to send was not single line");
    this#send_message(command)

  method receive_response() =
    let lines = this#receive_message() in
    debug_print "receive_response got message";
    let message = String.concat "\n" (List.tl lines) in
    if (List.length lines < 1) then
      this#error ("Received a empty message from the ASTServer");
    let kind = List.hd lines in
    if not (List.mem kind responses) then
        this#error ("Received an incomprehensible message from the ASTServer: \n" ^ message);
    if kind = response_abort then begin
      this#unload ();
      this#error ("ASTServer aborted while exetuting command: \n" ^ message)
    end;
    if kind = response_failure then
      this#error ("ASTServer could not execute command correctely: \n" ^ message);   
    let kind =
      if kind = response_success then SUCCESS
      else if kind = response_callback then CALLBACK
      else (this#error ("ASTServer internal inconsistency"); CALLBACK)
    in
    (kind, message)
end

let get_communication_channel _ = new socket_communication ()
