#ifndef GUI_H
#define GUI_H

void gui_init();
    //@ requires true;
    //@ ensures true;
  
struct widget;

//@ predicate window(struct widget* result); 
   
struct widget* gui_window_new();
    //@ requires true;
    //@ ensures window(result);

void gui_widget_show(struct widget* widget); // todo: generalize
    //@ requires window(widget);
    //@ ensures window(widget);

void gui_main();
    //@ requires true;
    //@ ensures true;

#endif