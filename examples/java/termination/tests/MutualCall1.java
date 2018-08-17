class MutualCall {

    static void bar()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        baz(); //~ should_fail
    }
    
    static void baz()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        bar();
    }

}
