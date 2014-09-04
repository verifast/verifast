class C {
    void m()
        //@ requires true;
        //@ ensures false;
    {
        //@ assume (false);
    }
}

class D extends C {
    void m()
        //@ requires this.getClass() == D.class;
        //@ ensures false;
    {
        if (this.getClass() == D.class)
        {
          //@ assume (false);
          throw null;
        }
    }
}

class E extends D { //~ should_fail
    E()
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
        E e = new E();
        C c = e;
        c.m();
        assert false;
    }
}