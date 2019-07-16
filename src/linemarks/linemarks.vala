using Gtk;
using Gdk;

class PixbufWithCache {
    public PixbufWithCache? next;
    
    public Pixbuf original;
    public int scaledSize;
    public Pixbuf? scaled;
    
    public PixbufWithCache(PixbufWithCache? next, Pixbuf original) {
        this.next = next;
        this.original = original;
        this.scaledSize = -1;
        this.scaled = null;
    }
    
    public Pixbuf get_at_size(int size) {
        if (scaledSize != size) {
            //stdout.printf("Cache miss\n");
            scaled = original.scale_simple(size, size, InterpType.BILINEAR);
            scaledSize = size;
        }
        return scaled;
    }
}

class LineMark {
    public Gtk.TextMark textMark;
    public PixbufWithCache pixbuf;
    public int line;
    public int column;
    
    public LineMark(Gtk.TextMark textMark, PixbufWithCache pixbuf) {
        this.textMark = textMark;
        this.pixbuf = pixbuf;
    }
    
    public void update_line_column_cache() {
        TextIter iter;
        textMark.get_buffer().get_iter_at_mark(out iter, textMark);
        line = iter.get_line();
        column = iter.get_line_offset();
        //stdout.printf("Updated line-column cache of linemark %p to (%d, %d)\n", this, line, column);
    }
}

public class LineMarksTable : GLib.Object {

    private PixbufWithCache? pixbufCache;
    
    private PixbufWithCache get_pixbuf_with_cache(Pixbuf pixbuf) {
        var cache = pixbufCache;
        while (cache != null && cache.original != pixbuf)
            cache = cache.next;
        if (cache == null)
            return pixbufCache = new PixbufWithCache(pixbufCache, pixbuf);
        else
            return cache;
    }
    
    internal LineMark[] lineMarks = {};
    private bool sorted = true;
    
    public void clear() {
        lineMarks.resize(0);
    }
    
    private void update_line_marks_line_column_cache() {
        for (int i = 0; i < lineMarks.length; i++) {
            LineMark mark = lineMarks[i];
            mark.update_line_column_cache();
        }
    }
    
    private static int compare_line_marks(LineMark **m1, LineMark **m2) {
        int result = (*m1)->line == (*m2)->line ? (*m1)->column - (*m2)->column : (*m1)->line - (*m2)->line;
        //stdout.printf("Comparing %p (%d, %d) with %p (%d, %d)... result=%d\n", *m1, (*m1)->line, (*m1)->column, *m2, (*m2)->line, (*m2)->column, result);
        return result;
    }
    
    private void sort_line_marks() {
        if (!sorted) {
            update_line_marks_line_column_cache();
            MyStuff.qsort_with_data(lineMarks, lineMarks.length, sizeof(LineMark *), compare_line_marks);
            sorted = true;
        }
    }
    
    public void add_line_mark(Gtk.TextMark textMark, Gdk.Pixbuf pixbuf) {
        lineMarks += new LineMark(textMark, get_pixbuf_with_cache(pixbuf));
        sorted = false;
    }
    
    public void add_line_mark_at_line_offset(TextBuffer buffer, int line, int offset, Gdk.Pixbuf pixbuf) {
        TextIter iter;
        buffer.get_iter_at_line_offset(out iter, line, offset);
        TextMark mark = buffer.create_mark(null, iter, true);
        add_line_mark(mark, pixbuf);
    }
    
    internal int lineHeight = 0;

    private int measure_line_height(SourceView view) {
        var layout = view.create_pango_layout("QWERTY");
        int height = 12;
        if (layout != null) {
            layout.get_pixel_size(null, out height);
        }
        lineHeight = height - 2;
        return lineHeight;
    }
    
    private int get_max_nb_marks_on_line(TextBuffer buffer) {
        // This code assumes that the marks are sorted.
        int max = 0;
        int currentLine = -1;
        int nb = 0; // Number of marks on the current line
        for (int i = 0; i < lineMarks.length; i++) {
            LineMark mark = lineMarks[i];
            TextMark m = mark.textMark;
            if (m.get_buffer() == buffer) {
                TextIter iter;
                buffer.get_iter_at_mark(out iter, m);
                if (iter.get_line() == currentLine) {
                    nb++;
                } else {
                    currentLine = iter.get_line();
                    nb = 1;
                }
                if (nb > max)
                    max = nb;
            }
        }
        return max;
    }
    
    //int messageCount = 0;

    internal int rendererWidth = 0;
    // invariant (holds only during a drawing cycle): all line marks in buffer lastBuffer at line > lastLineNumber are at index >= nextIndex
    internal TextBuffer? lastBuffer = null;
    internal int lastLineNumber = -1;
    internal int nextIndex = 0;
    
    private void size_func(SourceGutter gutter, CellRenderer renderer) {
        sort_line_marks();
        SourceView view = gutter.view;
        rendererWidth = measure_line_height(view) * get_max_nb_marks_on_line(view.get_buffer());
        lastBuffer = null;
        lastLineNumber = -1;
        nextIndex = 0;
        //stdout.printf("%05d: size_func called; lineHeight=%d\n", ++messageCount, lineHeight);
    }

    internal int lineNumber = -1;
    
    private void data_func(SourceGutter gutter, CellRenderer renderer, int lineNumber, bool currentLine) {
        //stdout.printf("%05d: data_func called with lineNumber=%d\n", ++messageCount, lineNumber);
        this.lineNumber = lineNumber;
    }
    
    public void show_in_source_view(Gtk.SourceView sourceView) {
        SourceGutter gutter = sourceView.get_gutter(TextWindowType.LEFT);
        LineMarksRenderer renderer = new LineMarksRenderer(this, gutter);
        gutter.insert(renderer, 0);
        gutter.set_cell_size_func(renderer, size_func);
        gutter.set_cell_data_func(renderer, data_func);
    }

}

class LineMarksRenderer : CellRenderer {

    LineMarksTable table;
    SourceGutter gutter;

    public LineMarksRenderer (LineMarksTable table, SourceGutter gutter) {
        GLib.Object ();
        this.table = table;
        this.gutter = gutter;
    }

    public override void get_size (Widget widget, Gdk.Rectangle? cell_area,
                                   out int x_offset, out int y_offset,
                                   out int width, out int height)
    {
        x_offset = 0;
        y_offset = 0;
        width = table.rendererWidth;
        height = table.lineHeight;
    }

    public override void render (Gdk.Window window, Widget widget,
                                 Gdk.Rectangle background_area,
                                 Gdk.Rectangle cell_area,
                                 Gdk.Rectangle expose_area,
                                 CellRendererState flags)
    {
        Cairo.Context ctx = Gdk.cairo_create (window);
        int x = background_area.x;
        TextBuffer buffer = gutter.view.get_buffer();
        if (table.lastBuffer != buffer || table.lastLineNumber >= table.lineNumber) {
            //stdout.printf("Restarting...\n");
            table.lastBuffer = buffer;
            table.nextIndex = 0;
        }
        for (; table.nextIndex < table.lineMarks.length; table.nextIndex++) {
            LineMark mark = table.lineMarks[table.nextIndex];
            TextMark m = mark.textMark;
            if (m.get_buffer() == buffer) {
                TextIter iter;
                buffer.get_iter_at_mark(out iter, m);
                if (iter.get_line() > table.lineNumber)
                    break;
                if (iter.get_line() == table.lineNumber) {
                    Gdk.cairo_rectangle(ctx, Rectangle() { x = x + 1, y = background_area.y + 1, width = table.lineHeight - 2, height = table.lineHeight - 2});
                    Gdk.cairo_set_source_pixbuf(ctx, mark.pixbuf.get_at_size(table.lineHeight - 2), x + 1, background_area.y + 1);
                    ctx.fill();
                    x += table.lineHeight;
                }
            }
        }
        table.lastLineNumber = table.lineNumber;
    }

}

public class SourceGutterTextColumn : GLib.Object {

    private string sizeText;
    private string[] lines = {};
    private CellRendererText renderer;
    private SourceGutter[] gutters;
    
    public SourceGutterTextColumn(string sizeText, float xalign) {
        this.sizeText = sizeText;
        renderer = new CellRendererText();
        renderer.xalign = xalign;
    }
    
    public void clear() {
        lines = {};
        foreach (var gutter in gutters) gutter.queue_draw();
    }
    
    public void add_line(string line) {
        lines += line;
        foreach (var gutter in gutters) gutter.queue_draw();
    }
    
    private void size_func(SourceGutter gutter, CellRenderer renderer_) {
        renderer.text = sizeText;
    }
    
    private void data_func(SourceGutter gutter, CellRenderer renderer_, int lineNumber, bool currentLine) {
        renderer.text = lineNumber < lines.length ? lines[lineNumber] : "";
    }
    
    public void show_in_source_view(Gtk.SourceView sourceView) {
        SourceGutter gutter = sourceView.get_gutter(TextWindowType.LEFT);
        gutters += gutter;
        gutter.insert(renderer, -5);
        gutter.set_cell_size_func(renderer, size_func);
        gutter.set_cell_data_func(renderer, data_func);
    }
    
}

