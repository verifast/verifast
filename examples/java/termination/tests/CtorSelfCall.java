class Foo {
    
    Foo()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        new Foo(); //~ should_fail
    }

}
