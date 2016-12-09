class Bar {

    static void bar()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        Baz.baz(); //~ should_fail
    }
    
}

class Baz {

    static void baz()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        Bar.bar();
    }

}
