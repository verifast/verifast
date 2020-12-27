// work in progress

#include "gui.h"
#include "stdio.h"

int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    struct widget *window = 0;
       
    gui_init();
    
    window = gui_window_new();
    gui_widget_show(window);
       
    gui_main();
}
