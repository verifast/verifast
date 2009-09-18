#ifndef GUI_H
#define GUI_H

//@ predicate gtk_initialized();

void gui_init();
    //@ requires true;
    //@ ensures [_]gtk_initialized();
  
struct widget;

//@ predicate widget(struct widget* widget); 
   
struct widget* gui_window_new();
    //@ requires true;
    //@ ensures widget(result);

void gui_widget_show(struct widget* widget);
    //@ requires widget(widget);
    //@ ensures widget(widget);

void gui_main();
    //@ requires [_]gtk_initialized();
    //@ ensures false; // does this ever return?

#endif
