class table =
  object
    method clear = ()
    method add (mark: Gtk.text_mark) (pixbuf: GdkPixbuf.pixbuf) = ()
    method show_in_source_view (view: GSourceView2.source_view) = ()
  end

let table () = new table

class source_gutter_text_column () =
  object
    method clear = ()
    method add_line (line: string) = ()
    method show_in_source_view (view: GSourceView2.source_view) = ()
  end

let source_gutter_text_column sizeText xalign = new source_gutter_text_column ()
