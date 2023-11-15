package foo;

class Bar {
    public static final short BAR = (byte)0x103;
    public static final short QUUX = (short) (Foo.FOO + BAR);
    public static final short BLA = (short)QUUX;
    //@ public static final short GHOST = 1;
    //@ public static final pair<int, int> PAIR = pair(GHOST, 2);

    private Bar() 
      //@ requires true;
      //@ ensures true;
    {
      
      this.m(Foo.FOO);
    }
    
    public void m(int s) 
      //@ requires true;
      //@ ensures true;
    {
    }
        
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        short tmp0 = 0;
        tmp0 = BLA;
        assert Foo.FOO == 12345;
        assert BAR == 3;
        assert QUUX == 12348;
        //@ assert GHOST == 1;
        //@ assert PAIR == pair(1, 2);
    }
    
}

class Foo {

    private Foo() 
      //@ requires true;
      //@ ensures true;
    {
    }
    public static final int FOO = 12345;
}

interface Baz {
    int ONE = 1;
    int TWO = 2;
}

class BazUser1 {
    static void user()
        //@ requires true;
        //@ ensures true;
    {
        assert Baz.ONE == 1;
    }
}

class BazUser2 implements Baz {
    void instanceMethod()
        //@ requires true;
        //@ ensures true;
    {
        assert TWO == 2;
    }
    
    static void staticMethod()
        //@ requires true;
        //@ ensures true;
    {
        assert TWO == 2;
    }
}