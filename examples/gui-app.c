// work in progress

#include "gui.h"
#include "stdio.h"

int main(int argc, char **argv)
    //@ requires 0 <= argc &*& [_]char_array(argv, argc);
    //@ ensures true;
{
    struct widget *window = 0;
       
    gui_init();
    
    window = gui_window_new();
    gui_widget_show(window);
       
    gui_main();
    
    return 0;
}
