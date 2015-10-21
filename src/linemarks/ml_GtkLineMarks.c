#include "linemarks.h"

#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/custom.h>

static void ml_GObject_finalize(value object) {
    g_object_unref(*(GObject **)Data_custom_val(object));
}

static struct custom_operations GObject_caml_custom_ops = {
    "GObject",
    ml_GObject_finalize,
    custom_compare_default,
    custom_compare_ext_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default
};

static value Val_GObject(GObject *object) {
    value result = caml_alloc_custom(&GObject_caml_custom_ops, sizeof(GObject *), 1, 1000);
    *(GObject **)Data_custom_val(result) = object;
    return result;
}

CAMLprim value ml_gtk_line_marks_create_table() {
    return Val_GObject(&(line_marks_table_new()->parent_instance));
}

CAMLprim value ml_gtk_line_marks_table_clear(value table) {
    line_marks_table_clear(*(LineMarksTable **)Data_custom_val(table));
    return Val_unit;
}

CAMLprim value ml_gtk_line_marks_table_add(value table, value mark, value pixbuf) {
   line_marks_table_add_line_mark(
       *(LineMarksTable **)Data_custom_val(table),
       GTK_TEXT_MARK(*(GObject **)Data_custom_val(mark)),
       GDK_PIXBUF(*(GObject **)Data_custom_val(pixbuf)));
   return Val_unit;
}

CAMLprim value ml_gtk_line_marks_table_show_in_source_view(value table, value view) {
    line_marks_table_show_in_source_view(
        *(LineMarksTable **)Data_custom_val(table),
        GTK_SOURCE_VIEW(*(GObject **)Data_custom_val(view)));
    return Val_unit;
}
