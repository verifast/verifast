//@ load_plugin trivial;  // Loads "trivial_verifast_plugin.cmxs"

void create_trivial_box();
    //@ requires true;
    //@ ensures #"0";

void incr();
    //@ requires #"0";
    //@ ensures #"1";

void decr();
    //@ requires #"1";
    //@ ensures #"0";

void test1()
    //@ requires true;
    //@ ensures true;
{
    create_trivial_box();
    incr();
    incr();
    decr();
    decr();
}

void test2()
    //@ requires true;
    //@ ensures true;
{
    create_trivial_box();
    incr();
    incr();
    decr();
} //~ should_fail // Function leaks trivial resource

void test3()
    //@ requires true;
    //@ ensures true;
{
    create_trivial_box();
    incr();
    incr();
    decr();
    decr();
    decr(); //~ should_fail // Insufficient trivial resource
}
