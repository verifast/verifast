using Gdk;
using Gtk;

class MyApp : Gtk.Window {

	public MyApp() {
		SourceView view = new SourceView();
		TextBuffer buffer = view.get_buffer();
		buffer.set_text("Line 1.\nLine 2 (left branch)\nLine 3 (left branch and right branch)\nLine 4");
		SourceGutterTextColumn textColumn = new SourceGutterTextColumn("99x", 1);
		for (int i = 0; i < 10; i++)
		    textColumn.addLine("%2dx".printf(i + 1));
		textColumn.show_in_source_view(view);
		Pixbuf branchLeft = new Pixbuf.from_file("../branch-left.png");
		Pixbuf branchRight = new Pixbuf.from_file("../branch-right.png");
		LineMarksTable table = new LineMarksTable();
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
