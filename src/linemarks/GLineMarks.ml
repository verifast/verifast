class table table =
  object
    method clear = GtkLineMarks.table_clear table
    method add mark pixbuf = GtkLineMarks.table_add table mark pixbuf
    method show_in_source_view (view: GSourceView2.source_view) = GtkLineMarks.table_show_in_source_view table view#as_view
  end

let table () = new table (GtkLineMarks.create_table ())
