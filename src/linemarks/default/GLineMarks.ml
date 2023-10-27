class table table =
  object
    method clear = GtkLineMarks.table_clear table
    method add mark pixbuf = GtkLineMarks.table_add table mark pixbuf
    method show_in_source_view (view: GSourceView2.source_view) = GtkLineMarks.table_show_in_source_view table view#as_view
  end

let table () = new table (GtkLineMarks.create_table ())

class source_gutter_text_column column =
  object
    method clear = GtkLineMarks.source_gutter_text_column_clear column
    method add_line line = GtkLineMarks.source_gutter_text_column_add_line column line
    method show_in_source_view (view: GSourceView2.source_view) = GtkLineMarks.source_gutter_text_column_show_in_source_view column view#as_view
  end

let source_gutter_text_column sizeText xalign = new source_gutter_text_column (GtkLineMarks.source_gutter_text_column_new sizeText xalign)
