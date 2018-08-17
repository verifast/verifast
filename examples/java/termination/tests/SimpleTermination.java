class SimpleTermination {

    static void foo()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant true;
            //@ decreases 10 - i;
        {
        }
    }

    static void bar()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant true;
            //@ decreases 10 - i;
        {
            foo();
        }
    }
    
}

class AnotherClass {

    AnotherClass()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {}

    static void quux()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        SimpleTermination.bar();
    }

}

class Foo {

    void bar()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        AnotherClass anotherClass = new AnotherClass();
    }

    static void foo()
        //@ requires true;
        //@ ensures true;
        //@ terminates;
    {
        Foo foo = new Foo(); // Default constructor is declared as 'terminates'.
        //foo.bar(); //TODO: allow this
    }

}