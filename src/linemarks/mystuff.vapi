namespace MyStuff {

    // Not using GLib.qsort_with_data; the semantics of this function changes between Vala versions due to a bug fix.
    [CCode (cheader_filename="glib.h", cname = "g_qsort_with_data")]
    void qsort_with_data([CCode (type = "gconstpointer")] void *elems, int count, size_t size, [CCode (type = "GCompareDataFunc")] GLib.CompareDataFunc<void **> compare_func);

}
