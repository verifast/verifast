// gtk implementation of gui.h
// compile: gcc -c gui-gtk.c `pkg-config --cflags --libs gtk+-2.0`

#include "gui.h"
#include <gtk/gtk.h>
#include "stdlib.h"

struct widget {
  GtkWidget* widget;
};

void gui_init()
{
  int argc = 0;
  char** argv = 0;
  gtk_init (&argc, &argv);
}


struct widget* gui_window_new()
{
  struct widget* widget = malloc(sizeof(struct widget));
  if(widget == 0) {
    abort();
  }
  widget->widget = gtk_window_new(GTK_WINDOW_TOPLEVEL);
  return widget;
}


void gui_widget_show(struct widget* widget)
{
  gtk_widget_show(widget->widget);
}

void gui_main() {
  gtk_main();
}
