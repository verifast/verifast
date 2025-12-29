void f()
//@ requires true;
//@ ensures true;
{
    "\0";
    //@ assert [_]chars(_, 2, {0, 0});
}
