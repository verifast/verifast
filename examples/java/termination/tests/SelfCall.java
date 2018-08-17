class SelfCall {

    static void foo()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        foo(); //~ should_fail
    }

}

