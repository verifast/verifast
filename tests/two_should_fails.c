void bar()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    baz(); //~ should_fail
}

void baz()
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    bar();
}

void quux()
    //@ requires true;
    //@ ensures true;
{
  /*@ assert false; @*/ //~ should_fail
}