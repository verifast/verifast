class C {
    C()
        //@ requires false;
        //@ ensures true;
    {
        assert false;
    }
}

class D extends C {
    D()  //~ should_fail
        //@ requires true;
        //@ ensures true;
    {
    }
}

class Program {
    static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        D d = new D();
    }
}