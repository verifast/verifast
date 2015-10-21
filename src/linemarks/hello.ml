let () =
  let app = GWindow.window () in
  let branchLeft = GdkPixbuf.from_file "../../bin/branch-left.png" in
  let branchRight = GdkPixbuf.from_file "../../bin/branch-right.png" in
  let table = GLineMarks.table () in
  let buffer = GSourceView2.source_buffer () in
  let addLineMark line column pixbuf =
    let iter = buffer#get_iter_at_char ~line column in
    let mark = buffer#create_mark iter in
    table#add mark pixbuf
  in
  let view = GSourceView2.source_view ~source_buffer:buffer () in
  buffer#set_text "Line 1.\nLine 2 (left branch)\nLine 3 (left branch and right branch)\nLine 4";
  addLineMark 2 24 branchRight;
  addLineMark 1 8 branchLeft;
  addLineMark 2 8 branchLeft;
  table#show_in_source_view view;
  let scrolledWindow = GBin.scrolled_window () in
  scrolledWindow#add view#coerce;
  app#add scrolledWindow#coerce;
  
  app#connect#destroy (fun () -> GMain.Main.quit ());
  app#show ();
  GMain.Main.main ()

(*
class MyApp : Gtk.Window {
	public MyApp() {
		Pixbuf branchLeft = new Pixbuf.from_file("/home/bartj/gtksourceview-extensions/branch-left.png");
		Pixbuf branchRight = new Pixbuf.from_file("/home/bartj/gtksourceview-extensions/branch-right.png");
		LineMarksTable table = new LineMarksTable();
		SourceView view = new SourceView();
		TextBuffer buffer = view.get_buffer();
		buffer.set_text("Line 1.\nLine 2 (left branch)\nLine 3 (left branch and right branch)\nLine 4");
		table.add_line_mark_at_line_offset(buffer, 1, 8, branchLeft);
		table.add_line_mark_at_line_offset(buffer, 2, 8, branchLeft);
		table.add_line_mark_at_line_offset(buffer, 2, 24, branchRight);
		table.show_in_source_view(view);
		ScrolledWindow scrolledWindow = new ScrolledWindow(null, null);
		scrolledWindow.add(view);
		add(scrolledWindow);
	}
	public static int main(string[] args) {
		Gtk.init(ref args);
		MyApp app = new MyApp();
		app.destroy.connect(Gtk.main_quit);
		app.show_all();
		Gtk.main();
		return 0;
	}
}
*)
