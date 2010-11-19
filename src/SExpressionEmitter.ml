open Verifast
open SExpressions

let with_open_file (filename : string) (func : out_channel -> unit) =
  let channel = open_out filename in
  try
    func channel
  with
      e -> begin 
        flush channel;
        close_out channel
      end

let emit (target_file : string) (packages : package list) =
  let emit_to channel =
    let output_string = output_string channel
    in
    output_string "..."
  in
  with_open_file target_file emit_to
