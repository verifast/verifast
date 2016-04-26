let get_first_line_tokens text =
  let n = String.length text in
  let rec first_line_tokens i =
    if i = n then
      []
    else
      match text.[i] with
        'A'..'Z'|'a'..'z'|'0'..'9'|'_' -> ident_token i (i + 1)
      | ' '|'\t' -> first_line_tokens (i + 1)
      | '\r'|'\n' -> []
      | c -> Printf.sprintf "%c" c::first_line_tokens (i + 1)
  and ident_token start i =
    match if i = n then None else Some text.[i] with
      Some ('A'..'Z'|'a'..'z'|'0'..'9'|'_') -> ident_token start (i + 1)
    | _ -> String.sub text start (i - start)::first_line_tokens i
  in
  first_line_tokens 0

type file_options = {file_opt_annot_char: char; file_opt_tab_size: int}

let get_file_options text =
  let tokens = get_first_line_tokens text in
  let rec iter annotChar tabSize toks =
    match toks with
      "verifast_annotation_char"::":"::c::toks when String.length c = 1 -> iter c.[0] tabSize toks
    | "tab_size"::":"::n::toks ->
      begin
        try
          iter annotChar (int_of_string n) toks
        with Failure "int_of_string" -> iter annotChar tabSize toks
      end
    | tok::toks -> iter annotChar tabSize toks
    | [] -> {file_opt_annot_char=annotChar; file_opt_tab_size=tabSize}
  in
  iter '@' 8 tokens

let readFile chan =
  let count = ref 0 in
  let rec iter () =
    let buf = String.create 60000 in
    let result = input chan buf 0 60000 in
    count := !count + result;
    if result = 0 then [] else (buf, result)::iter()
  in
  let chunks = iter() in
  let s = String.create !count in
  let rec iter2 chunks offset =
    match chunks with
      [] -> ()
    | (buf, size)::chunks ->
      String.blit buf 0 s offset size;
      iter2 chunks (offset + size)
  in
  iter2 chunks 0;
  s

let strip_annotations fin fout =
  let text = readFile fin in
  let n = String.length text in
  let {file_opt_annot_char=annotChar} = get_file_options text in
  let rec iter i0 white i =
    if i = n then
      output fout text i0 (n - i0)
    else
      match text.[i] with
        '/' when i + 3 <= n && (text.[i + 1] = '/' || text.[i + 1] = '*') && text.[i + 2] = annotChar ->
        begin match text.[i + 1] with
          '/' ->
          let after_annot eol j =
            if white > 0 && text.[white - 1] <> '\n' && text.[white - 1] <> '\r' then iter eol eol eol else iter j j j
          in
          let rec eat_annot j =
            if j = n then
              output fout text i0 (white - i0)
            else
              match text.[j] with
                '\r' ->
                let j' =
                  if j + 1 < n && text.[j + 1] = '\n' then j + 2 else j + 1
                in
                output fout text i0 (white - i0);
                after_annot j j'
              | '\n' ->
                output fout text i0 (white - i0);
                after_annot j (j + 1)
              | _ -> eat_annot (j + 1)
          in
          eat_annot (i + 3)
        | '*' ->
          let rec eat_trailing_white_lines j0 =
            let rec iter' j =
              if j = n then
                output fout text i0 (white - i0)
              else
                match text.[j] with
                  ' ' | '\t' -> iter' (j + 1)
                | '\r' | '\n' -> eat_trailing_white_lines (j + 1)
                | _ -> output fout text i0 (white - i0); iter j0 j0 j
            in
            iter' j0
          in
          let rec eat_annot j =
            if j = n then
              output fout text i0 (white - i0)
            else
              match text.[j] with
                c when c = annotChar && j + 3 <= n && text.[j + 1] = '*' && text.[j + 2] = '/' ->
                eat_trailing_white_lines (j + 3)
              | _ -> eat_annot (j + 1)
          in
          eat_annot (i + 3)
        | _ -> assert false
        end
      | ' ' | '\t' -> iter i0 white (i + 1)
      | _ -> let i = i + 1 in iter i0 i i
  in
  iter 0 0 0

let strip_comments fin fout =
  let text = readFile fin in
  let n = String.length text in
  let rec iter i0 white i text_on_line =
    if i = n then
      output fout text i0 (white - i0)
    else
      match text.[i] with
        '/' when i + 1 <= n && (text.[i + 1] = '/' || text.[i + 1] = '*') ->
        begin match text.[i + 1] with
          '/' ->
          let rec eat_comment j =
            if j = n then
              iter i0 white j text_on_line
            else
              match text.[j] with
              | '\r'|'\n' ->
                iter i0 white j text_on_line
              | _ ->
                eat_comment (j + 1)
          in
          eat_comment (i + 2)
        | '*' ->
          output fout text i0 (white - i0);
          let rec eat_comment j text_on_line =
            if j = n then
              iter n n n text_on_line
            else if text.[j] = '*' && j + 1 < n && text.[j + 1] = '/' then
              let i = j + 2 in iter i i i text_on_line
            else if text.[j] = '\n' && text_on_line then begin
              output_string fout "\n";
              eat_comment (j + 1) false
            end else if text.[j] = '\r' && text_on_line then begin
              if j + 1 < n && text.[j + 1] = '\n' then begin
                output_string fout "\r\n";
                eat_comment (j + 2) false
              end else begin
                output_string fout "\r";
                eat_comment (j + 1) false
              end
            end else
              eat_comment (j + 1) text_on_line
          in
          eat_comment (i + 2) text_on_line
        end
      | ' ' | '\t' -> iter i0 white (i + 1) text_on_line
      | '\n'|'\r' ->
        let i' = if text.[i] = '\r' && i + 1 < n && text.[i + 1] = '\n' then i + 2 else i + 1 in
        if text_on_line then begin
          if white = i then
            iter i0 i' i' false
          else begin
            output fout text i0 (white - i0);
            iter i i' i' false
          end
        end else begin
          output fout text i0 (white - i0);
          iter i' i' i' false
        end
      | _ -> let i = i + 1 in iter i0 i i true
  in
  iter 0 0 0 false

let () =
  match Sys.argv with
    [| _ |] -> strip_annotations stdin stdout
  | [| _; "--all-comments" |] -> strip_comments stdin stdout
  | _ ->
    print_endline "vfstrip: Copies stdin to stdout, removing all VeriFast annotations";
    print_endline "Usage: vfstrip < inputfile > outputfile";
    print_endline "";
    print_endline "vfstrip --all-comments: Copies stdin to stdout, removing all comments and blank lines";
    print_endline "Usage: vfstrip --all-comments < inputfile > outputfile"
