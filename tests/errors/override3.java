interface I {
    void m();
        //@ requires true;
        //@ ensures false;
}

class D implements I {
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
        I i = d;
        i.m();
        assert false;
    }
}