class Foo {
    
    Foo()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        new Bar(); //~ should_fail
    }

}

class Bar {

    Bar()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        new Foo();
    }

}