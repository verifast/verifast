class source_buffer buffer =
  object
    inherit GText.buffer buffer#as_buffer
  end

class source_view (source_buffer: source_buffer) view () =
  object
    inherit GText.view view#as_view
    val mutable show_line_numbers = false
    val mutable draw_spaces: [ `SPACE | `TAB ] list = []
    method source_buffer = source_buffer
    method show_line_numbers = show_line_numbers
    method set_show_line_numbers (enable:bool) = show_line_numbers <- enable
    method draw_spaces = draw_spaces
    method set_draw_spaces flags = draw_spaces <- flags
    method set_tab_width (size: int) = ()
  end

let source_view ?source_buffer ~packing () =
  let buffer = match source_buffer with None -> GText.buffer () | Some sbuf -> (sbuf :> GText.buffer) in
  let view = GText.view ~packing ~buffer () in
  view#set_pixels_above_lines 1;
  view#set_pixels_below_lines 1;
  new source_view (new source_buffer buffer) view ()
