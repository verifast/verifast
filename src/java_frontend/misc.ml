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

(* Lists *)
let remove_last lst =
  List.rev (List.tl (List.rev lst))
let get_last lst =
  List.hd (List.rev lst)

(*  Strings *)
let rec split_string c s =
  try 
  begin
    let i = String.index s c in
    (String.sub s 0 i)::split_string c (String.sub s (i+1) ((String.length s) - (i+1)))
  end
  with Not_found ->
    [s]

(* Paths *)
let concat path1 path2 =
  if path1 = "" || path1 = "." then path2 else path1 ^ Filename.dir_sep ^ path2

let split_path path =
  let parts = split_string (String.get Filename.dir_sep 0) path in
  if (List.length parts) > 2 then
    (String.concat Filename.dir_sep (List.rev (List.tl (List.rev parts))), List.hd (List.rev parts))
  else
    ("", path)

(* Functions *)
let apply_option f a =
  match a with
    Some a' -> Some (f a')
  | None -> None
