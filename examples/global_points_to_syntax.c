#include "stdlib.h"

static int global1 = -10;
static int global2 = 10;
static unsigned int global3 = 20; 
static char global4 = 'a';
static char global5 = 'b';

void modify_primitive_globals_old_syntax()
    /*@ 
        requires integer(&global1, ?val1) &*& integer(&global2, ?val2) &*&
            u_integer(&global3, ?val3) &*& character(&global4, ?val4) &*& character(&global5, ?val5);
    @*/
    /*@ 
        ensures integer(&global1, val1 + 5) &*& integer(&global2, val2 + 5) &*& 
            u_integer(&global3, val3 + 5) &*& character(&global4, (char)(val4 + 5)) &*& character(&global5, (char)(val5 + 5));
    @*/
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

void modify_primitive_globals_new_syntax()
    //@ requires global1 |-> ?val1 &*& global2 |-> ?val2 &*& global3 |-> ?val3 &*& global4 |-> ?val4 &*& global5 |-> ?val5;
    //@ ensures global1 |-> val1 + 5 &*& global2 |-> val2 + 5 &*& global3 |-> val3 + 5 &*& global4 |-> (char)(val4 + 5) &*& global5 |-> (char)(val5 + 5);
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

int main() //@ : main_full(global_points_to_syntax)
    //@ requires module(global_points_to_syntax, true);
    //@ ensures true;
{
    //@ open_module();

    //@ assert global1 == -10 && global2 == 10 && global3 == 20 && global4 == 'a' && global5 == 'b';
    modify_primitive_globals_old_syntax();
    //@ assert global1 == -5 && global2 == 15 && global3 == 25 && global4 == 'f' && global5 == 'g';
    modify_primitive_globals_new_syntax();
    //@ assert global1 == 0 && global2 == 20 && global3 == 30 && global4 == 'k' && global5 == 'l';
    
    //@ leak global1 |-> _ &*& global2 |-> _ &*& global3 |-> _ &*& global4 |-> _ &*& global5 |-> _;

    return 0;
}


