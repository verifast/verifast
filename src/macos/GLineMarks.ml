class table =
  object
    method clear = ()
    method add (mark: Gtk.text_mark) (pixbuf: GdkPixbuf.pixbuf) = ()
    method show_in_source_view (view: GSourceView2.source_view) = ()
  end

let table () = new table
