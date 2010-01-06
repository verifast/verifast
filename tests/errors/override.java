class C {
    void m()
        //@ requires true;
        //@ ensures false;
    {
        throw null;
    }
}

class D extends C {
    D()
        //@ requires true;
        //@ ensures true;
    {}
    
    void m()
        //@ requires false; //~ should_fail
        //@ ensures false;
    {
    }
}

class Program {
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        D d = new D();
        C c = d;
        c.m();
        assert false;
    }
}