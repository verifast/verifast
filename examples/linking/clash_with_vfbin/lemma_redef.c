//@ #include "raw_ghost_lists.gh"

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    //@ create_raw_ghost_list();
    *((int *)0) = 5; //~allow_dead_code
    return 0; //~allow_dead_code
}