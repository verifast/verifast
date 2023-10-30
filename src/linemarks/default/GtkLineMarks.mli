type table

external create_table: unit -> table = "ml_gtk_line_marks_create_table"
external table_clear: table -> unit = "ml_gtk_line_marks_table_clear"
external table_add: table -> Gtk.text_mark -> GdkPixbuf.pixbuf -> unit = "ml_gtk_line_marks_table_add"
external table_show_in_source_view: table -> Gtk.text_view Gtk.obj -> unit = "ml_gtk_line_marks_table_show_in_source_view"

type source_gutter_text_column

external source_gutter_text_column_new: string -> float -> source_gutter_text_column = "ml_source_gutter_text_column_new"
external source_gutter_text_column_clear: source_gutter_text_column -> unit = "ml_source_gutter_text_column_clear"
external source_gutter_text_column_add_line: source_gutter_text_column -> string -> unit = "ml_source_gutter_text_column_add_line"
external source_gutter_text_column_show_in_source_view: source_gutter_text_column -> Gtk.text_view Gtk.obj -> unit = "ml_source_gutter_text_column_show_in_source_view"
