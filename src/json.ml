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

type json_token_type = LBracket | RBracket | LBrace | RBrace | Comma | Colon | NullToken | True | False | Integer | String | Eof

let string_of_token_type = function
  LBracket -> "'['"
| RBracket -> "']'"
| LBrace -> "'{'"
| RBrace -> "'}'"
| Comma -> "','"
| Colon -> "':'"
| NullToken -> "'null'"
| True -> "'true'"
| False -> "'false'"
| Integer -> "integer"
| String -> "string"
| Eof -> "end of input"

type json_lexer = {
  text: string;
  mutable pos: int;
  mutable tokenStart: int;
  mutable tokenType: json_token_type;
  tokenValue: Buffer.t;
}

let peek {text; pos} =
  if pos < String.length text then
    text.[pos]
  else
    '\x00'

let junk lexer =
  lexer.pos <- lexer.pos + 1

exception JsonException of int * string

let lexer_error lexer msg =
  raise (JsonException (lexer.pos, msg))

let expect lexer c =
  if peek lexer <> c then lexer_error lexer (Printf.sprintf "%c expected" c);
  junk lexer
  
let next_json_token lexer =
  let rec iter () =
    lexer.tokenStart <- lexer.pos;
    match peek lexer with
      '\x00' -> Eof
    | ' '|'\n'|'\r'|'\t' -> junk lexer; iter ()
    | '"' ->
      junk lexer;
      Buffer.clear lexer.tokenValue;
      let rec parse_string () =
        match peek lexer with
          '\x00' -> lexer_error lexer "Unexpected EOF inside string literal"
        | '"' -> junk lexer; String
        | '\\' ->
          junk lexer;
          begin match peek lexer with
            '\\' -> junk lexer; Buffer.add_char lexer.tokenValue '\\'; parse_string ()
          | 'n' -> junk lexer; Buffer.add_char lexer.tokenValue '\n'; parse_string ()
          | 'r' -> junk lexer; Buffer.add_char lexer.tokenValue '\r'; parse_string ()
          | 't' -> junk lexer; Buffer.add_char lexer.tokenValue '\t'; parse_string ()
          | 'u' ->
            junk lexer;
            let parse_hex_digit () =
              match peek lexer with
                '0'..'9' as c -> junk lexer; Char.code c - Char.code '0'
              | 'A'..'F' as c -> junk lexer; Char.code c - Char.code 'A' + 10
              | 'a'..'f' as c -> junk lexer; Char.code c - Char.code 'a' + 10
              | _ -> lexer_error lexer "Bad Unicode escape in string literal"
            in
            let parse_hex_16bit_number () =
              let d1 = parse_hex_digit () in
              let d2 = parse_hex_digit () in
              let d3 = parse_hex_digit () in
              let d4 = parse_hex_digit () in
              d1 lsl 12 + d2 lsl 8 + d3 lsl 4 + d4
            in
            let utf16 = parse_hex_16bit_number () in
            (* Convert UTF-16-encoded character into UTF-8-encoded character *)
            if utf16 <= 0x7f then
              Buffer.add_char lexer.tokenValue (Char.chr utf16)
            else if utf16 <= 0x7ff then begin
              Buffer.add_char lexer.tokenValue (Char.chr ((utf16 lsr 6) lor 0b11000000));
              Buffer.add_char lexer.tokenValue (Char.chr ((utf16 land 0b00111111) lor 0b10000000))
            end else if utf16 <= 0xD7FF || 0xE000 <= utf16 then begin
              Buffer.add_char lexer.tokenValue (Char.chr ((utf16 lsr 12) lor 0b11100000));
              Buffer.add_char lexer.tokenValue (Char.chr (((utf16 lsr 6) land 0b00111111) lor 0b10000000));
              Buffer.add_char lexer.tokenValue (Char.chr ((utf16 land 0b00111111) lor 0b10000000))
            end else if utf16 <= 0xDBFF then begin
              (* High surrogate. Must be followed by low surrogate. *)
              expect lexer '\\';
              expect lexer 'u';
              let utf16' = parse_hex_16bit_number () in
              if 0xDC00 <= utf16' && utf16' <= 0xDFFF then begin
                let scalarValue = 0x10000 + ((utf16 land 0b1111111111) lsl 10) + (utf16' land 0b1111111111) in
                Buffer.add_char lexer.tokenValue (Char.chr ((scalarValue lsr 18) lor 0b11110000));
                Buffer.add_char lexer.tokenValue (Char.chr (((scalarValue lsr 12) land 0b00111111) lor 0b10000000));
                Buffer.add_char lexer.tokenValue (Char.chr (((scalarValue lsr 6) land 0b00111111) lor 0b10000000));
                Buffer.add_char lexer.tokenValue (Char.chr ((scalarValue land 0b00111111) lor 0b10000000))
              end else
                raise (JsonException (lexer.pos - 12, "Unpaired high surrogate"))
            end else
              raise (JsonException (lexer.pos - 6, "Unpaired low surrogate"));
            parse_string ()
          | '"' -> junk lexer; Buffer.add_char lexer.tokenValue '"'; parse_string ()
          | _ -> lexer_error lexer "Unsupported escape sequence inside string literal"
          end
        | c -> junk lexer; Buffer.add_char lexer.tokenValue c; parse_string ()
      in
      parse_string ()
    | '-'|'0'..'9' as c ->
      junk lexer;
      Buffer.clear lexer.tokenValue;
      Buffer.add_char lexer.tokenValue c;
      let rec parse_number () =
        match peek lexer with
          '0'..'9' as c -> junk lexer; Buffer.add_char lexer.tokenValue c; parse_number ()
        | _ -> Integer
      in
      parse_number ()
    | 'n' ->
      junk lexer;
      expect lexer 'u';
      expect lexer 'l';
      expect lexer 'l';
      NullToken
    | 't' ->
      junk lexer;
      expect lexer 'r';
      expect lexer 'u';
      expect lexer 'e';
      True
    | 'f' ->
      junk lexer;
      expect lexer 'a';
      expect lexer 'l';
      expect lexer 's';
      expect lexer 'e';
      False
    | '{' -> junk lexer; LBrace
    | '}' -> junk lexer; RBrace
    | '[' -> junk lexer; LBracket
    | ']' -> junk lexer; RBracket
    | ':' -> junk lexer; Colon
    | ',' -> junk lexer; Comma
    | _ -> lexer_error lexer "Illegal character"
  in
  let tokenType = iter () in
  lexer.tokenType <- tokenType

let mk_json_lexer text =
  let lexer = {text; pos=0; tokenStart=0; tokenType=Eof; tokenValue=Buffer.create 64} in
  next_json_token lexer;
  lexer

let lexer_get_value lexer =
  Buffer.contents lexer.tokenValue

let parse_error lexer msg =
  raise (JsonException (lexer.tokenStart, msg))

let expect_token lexer tokenType =
  if lexer.tokenType <> tokenType then parse_error lexer (string_of_token_type tokenType ^ " expected");
  next_json_token lexer

let parse_json text =
  let lexer = mk_json_lexer text in
  let rec iter () =
    match lexer.tokenType with
      NullToken -> next_json_token lexer; Null
    | True -> next_json_token lexer; B true
    | False -> next_json_token lexer; B false
    | String -> let value = lexer_get_value lexer in next_json_token lexer; S value
    | Integer ->
      let value = lexer_get_value lexer in
      begin match int_of_string_opt value with
        Some i -> next_json_token lexer; I i
      | None -> parse_error lexer "The integer is outside of the range supported by this JSON parser"
      end
    | LBrace ->
      next_json_token lexer;
      begin match lexer.tokenType with
        RBrace -> next_json_token lexer; O []
      | _ ->
        let rec parse_object props =
          if lexer.tokenType <> String then parse_error lexer "String expected";
          let key = lexer_get_value lexer in
          next_json_token lexer;
          expect_token lexer Colon;
          let value = iter () in
          let props = (key, value)::props in
          match lexer.tokenType with
            RBrace -> next_json_token lexer; O (List.rev props)
          | _ ->
            expect_token lexer Comma;
            parse_object props
        in
        parse_object []
      end
    | LBracket ->
      next_json_token lexer;
      begin match lexer.tokenType with
        RBracket -> next_json_token lexer; A []
      | _ ->
        let rec parse_array elems =
          let elem = iter () in
          let elems = elem::elems in
          match lexer.tokenType with
            RBracket -> next_json_token lexer; A (List.rev elems)
          | _ ->
            expect_token lexer Comma;
            parse_array elems
        in
        parse_array []
      end
    | _ -> parse_error lexer ("Unexpected JSON token: " ^ string_of_token_type lexer.tokenType)
  in
  let json = iter () in
  expect_token lexer Eof;
  json
