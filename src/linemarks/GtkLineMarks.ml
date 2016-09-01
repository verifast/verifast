type table = Obj.t

external create_table: unit -> table = "ml_gtk_line_marks_create_table"
external table_clear: table -> unit = "ml_gtk_line_marks_table_clear"
external table_add: table -> Gtk.text_mark -> GdkPixbuf.pixbuf -> unit = "ml_gtk_line_marks_table_add"
external table_show_in_source_view: table -> Gtk.text_view Gtk.obj -> unit = "ml_gtk_line_marks_table_show_in_source_view"
