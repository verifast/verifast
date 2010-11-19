open Format
open Big_int


type sexpression =
  | List of sexpression list
  | Symbol of string
  | Keyword of string
  | Number of big_int

let format_sexpression formatter sexpr =
  let box ?(indent = 0) contents =
    pp_open_box formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let hbox contents =
    pp_open_hbox formatter ();
    contents ();
    pp_close_box formatter ()
  in
  let hvbox ?(indent = 0) contents =
    pp_open_hvbox formatter indent;
    contents ();
    pp_close_box formatter ()
  in
  let verbatim str =
    box (fun () -> pp_print_string formatter str)
  in
  let flush () =
    pp_print_flush formatter ()
  in
  let rec format sexpr =
    match sexpr with
      | Symbol str -> verbatim str
      | Keyword str -> verbatim (":" ^ str)
      | Number n -> verbatim (string_of_big_int n)
      | List xs ->
	hbox begin fun () ->
	  verbatim "(";
	  begin
	    match xs with
	      | [] -> ()
	      | [x] ->
		box begin fun () ->
		  format x;
		end
	      | [x; y] ->
		hvbox begin fun () ->
		  format x;
		  pp_print_break formatter 1 1;
		  format y
		end
	      | (x :: y :: xs) ->
		hbox begin fun () ->
		  format x;
		  pp_print_space formatter ();
		  hvbox begin fun () ->
		    format y;
		    List.iter begin fun z ->
		      pp_print_space formatter ();
		      format z
		    end xs
		  end
		end
	  end;
	  verbatim ")"
	end
  in
  format sexpr;
  flush ()

let string_of_sexpression sexpr =
  let buffer = Buffer.create 1024 in
  let formatter = formatter_of_buffer buffer in
  format_sexpression formatter sexpr;
  Buffer.contents buffer
