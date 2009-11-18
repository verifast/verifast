package foo;

class Bar {
    public static final int QUUX = Foo.FOO + Bar.BAR;
    public static final int BAR = (byte)0x103;
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        assert Foo.FOO == 12345;
        assert Bar.BAR == 3;
        assert Bar.QUUX == 12348;
    }
}

class Foo {
    public static final int FOO = 12345;
}
