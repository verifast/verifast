let (|>) x f = f x

type json =
  S of string
| I of int
| F of float
| Null
| B of bool
| A of json list
| O of (string * json) list

let hex_char_of_int i =
  char_of_int
    (if i <= 9 then int_of_char '0' + i else int_of_char 'a' - 10 + i)

let buffer_add_json_char buf c =
  match c with
    '"' -> Buffer.add_string buf "\\\""
  | '\\' -> Buffer.add_string buf "\\\\"
  | '\n' -> Buffer.add_string buf "\\n"
  | '\r' -> Buffer.add_string buf "\\r"
  | '\x00'..'\x1f' ->
    Buffer.add_string buf "\\u00";
    let c = int_of_char c in
    Buffer.add_char buf (hex_char_of_int (c lsr 4));
    Buffer.add_char buf (hex_char_of_int (c land 0xf))
  | _ -> Buffer.add_char buf c

let buffer_add_json_string buf s =
  Buffer.add_char buf '"';
  for i = 0 to String.length s - 1 do
    buffer_add_json_char buf s.[i]
  done;
  Buffer.add_char buf '"'

let buffer_add_json buf json =
  let rec iter json =
    match json with
      S s -> buffer_add_json_string buf s
    | I i -> Printf.bprintf buf "%d" i
    | F f ->
      begin match classify_float f with
        FP_infinite | FP_nan -> failwith "Cannot represent infinity or NaN as JSON number"
      | _ -> Printf.bprintf buf "%.17e" f
      end
    | Null -> Printf.bprintf buf "null"
    | B b -> Buffer.add_string buf (if b then "true" else "false")
    | A [] -> Buffer.add_string buf "[]"
    | A (v::vs) ->
      Buffer.add_char buf '[';
      iter v;
      vs |> List.iter begin fun v ->
        Buffer.add_char buf ',';
        iter v
      end;
      Buffer.add_char buf ']'
    | O [] -> Buffer.add_string buf "{}"
    | O ((k, v)::kvs) ->
      Buffer.add_char buf '{';
      buffer_add_json_string buf k;
      Buffer.add_char buf ':';
      iter v;
      kvs |> List.iter begin fun (k, v) ->
        Buffer.add_char buf ',';
        buffer_add_json_string buf k;
        Buffer.add_char buf ':';
        iter v
      end;
      Buffer.add_char buf '}'
  in
  iter json

let print_json_endline json =
  let buf = Buffer.create 1024 in
  buffer_add_json buf json;
  Buffer.output_buffer stdout buf;
  print_newline ()
