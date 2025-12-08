type rocq_writer = {
  mutable buf: Buffer.t option; (* None means no output *)
  indent_unit: string;
  mutable last_indent: int; (* Number of indent units last printed *)
  mutable indent: int; (* Number of indent units currently active *)
  mutable pending_separator: string option;
  mutable pending_newline: bool;
  mutable need_parens: bool;
}

let rocq_create_writer enabled : rocq_writer =
  {
    buf = if enabled then Some (Buffer.create 65536) else None;
    indent_unit = "    ";
    last_indent = 0;
    indent = 0;
    pending_separator = None;
    pending_newline = false;
    need_parens = false;
  }

let rocq_suppress_output writer body =
  let old_buf = writer.buf in
  let old_pending_separator = writer.pending_separator in
  let old_pending_newline = writer.pending_newline in
  writer.buf <- None;
  let result = body () in
  writer.buf <- old_buf;
  writer.pending_separator <- old_pending_separator;
  writer.pending_newline <- old_pending_newline;
  result

let rocq_set_need_parens writer need_parens body =
  let needed_parens = writer.need_parens in
  writer.need_parens <- need_parens;
  let result = body () in
  writer.need_parens <- needed_parens;
  result

let rocq_write_to_channel writer oc =
  match writer.buf with
  | Some buf ->
    Buffer.output_buffer oc buf

let rocq_do_print_newline writer =
  writer.last_indent <- writer.indent;
  match writer.buf with
  | None -> ()
  | Some buf ->
    Buffer.add_string buf "\n";
    for _ = 1 to writer.indent do
      Buffer.add_string buf writer.indent_unit
    done

let rocq_print writer s =
  match writer.buf with
  | None -> ()
  | Some buf ->
    Buffer.add_string buf s

let rocq_flush_pending writer =
  begin match writer.pending_separator with
  | Some sep ->
      rocq_print writer sep;
      writer.pending_separator <- None
  | None -> ()
  end;
  if writer.pending_newline then begin
    rocq_do_print_newline writer;
    writer.pending_newline <- false
  end

let rocq_indent writer body =
  writer.indent <- writer.indent + 1;
  let result = body () in
  writer.indent <- writer.indent - 1;
  result

let rocq_print writer s =
  rocq_flush_pending writer;
  rocq_print writer s

let rocq_print_data writer f data =
  match writer.buf with
  | None -> ()
  | Some _ ->
    f writer data

let rocq_print_string_literal writer s =
  rocq_print writer "\"";
  rocq_print writer s; (* TODO: escape special chars *)
  rocq_print writer "\""

let rocq_print_bool_literal writer b =
  rocq_print writer (if b then "true" else "false")

let rocq_print_small_list writer body =
  rocq_set_need_parens writer false @@ fun () ->
  rocq_print writer "[";
  let result = body () in
  writer.pending_separator <- None;
  rocq_print writer "]";
  result

let rocq_print_small_list_element writer body =
  let result = body () in
  writer.pending_separator <- Some "; ";
  result

let rocq_print_small_record writer body =
  rocq_set_need_parens writer false @@ fun () ->
  rocq_print writer "{| ";
  let result = body () in
  writer.pending_separator <- None;
  rocq_print writer " |}";
  result

let rocq_print_small_record_field writer field_name body =
  rocq_print writer field_name;
  rocq_print writer " := ";
  let result = body () in
  writer.pending_separator <- Some "; ";
  result

let rocq_print_big_list writer body =
  rocq_set_need_parens writer false @@ fun () ->
  rocq_print writer "[";
  writer.pending_newline <- true;
  let result = rocq_indent writer body in
  writer.pending_newline <- false;
  writer.pending_separator <- None;
  if writer.last_indent <> writer.indent then
    rocq_do_print_newline writer;
  rocq_print writer "]";
  result

let rocq_print_big_list_element writer body =
  let result = body () in
  writer.pending_separator <- Some ";";
  writer.pending_newline <- true;
  result

let rocq_print_big_record writer body =
  rocq_set_need_parens writer false @@ fun () ->
  rocq_print writer "{|";
  writer.pending_newline <- true;
  let result = rocq_indent writer body in
  writer.pending_newline <- false;
  writer.pending_separator <- None;
  if writer.last_indent <> writer.indent then
    rocq_do_print_newline writer;
  rocq_print writer "|}";
  result

let rocq_print_big_record_field writer field_name body =
  rocq_print writer field_name;
  rocq_print writer " := ";
  let result = body () in
  writer.pending_separator <- Some ";";
  writer.pending_newline <- true;
  result

let rocq_print_tuple writer body =
  rocq_set_need_parens writer false @@ fun () ->
  rocq_print writer "(";
  let result = body () in
  writer.pending_separator <- None;
  rocq_print writer ")";
  result

let rocq_print_tuple_element writer body =
  let result = body () in
  writer.pending_separator <- Some ", ";
  result

let rocq_print_ident writer ident =
  rocq_print writer ident

let rocq_print_parens_if_needed writer body =
  if writer.need_parens then begin
    rocq_print writer "(";
    writer.need_parens <- false;
    let result = body () in
    rocq_print writer ")";
    writer.need_parens <- true;
    result
  end else
    body ()

let rocq_print_application writer func_name body =
  rocq_print_parens_if_needed writer @@ fun () ->
  rocq_print writer func_name;
  let result = body () in
  result

let rocq_print_argument writer body =
  rocq_print writer " ";
  writer.need_parens <- true;
  let result = body () in
  writer.need_parens <- false;
  result

let rocq_print_nat writer n =
  rocq_print writer (Printf.sprintf "%d%%nat" n)

let rocq_print_N writer n =
  rocq_print writer (Printf.sprintf "%s%%N" n)

let rocq_print_Q writer n =
  rocq_print writer (Printf.sprintf "%s%%Q" (Num.string_of_num n))

type term =
| Ident of string
| StringLiteral of string
| RealLiteral of Num.num
| App of string * term list
| List of term list

let rocq_print_small_term writer term =
  let rec print_term term =
    match term with
    | Ident s ->
      rocq_print_ident writer s
    | StringLiteral s ->
      rocq_print_string_literal writer s
    | RealLiteral n ->
      rocq_print_Q writer n
    | App (f, args) ->
      rocq_print_application writer f @@ fun () ->
      args |> List.iter @@ fun arg ->
        rocq_print_argument writer (fun () -> print_term arg)
    | List elements ->
      rocq_print_small_list writer @@ fun () ->
      elements |> List.iter @@ fun elem ->
        rocq_print_small_list_element writer @@ fun () ->
        print_term elem
  in
  print_term term

let rocq_print_big_term writer term =
  rocq_print_small_term writer term (* TODO: specialize *)

let rocq_print_symex_step_terminator writer =
  rocq_print_ident writer ";;";
  rocq_do_print_newline writer