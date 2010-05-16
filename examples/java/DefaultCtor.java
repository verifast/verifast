class Foo {

    int x;
    short y;
    byte z;
    Object o;
    Object[] p;

}

class Bar extends Foo {

    int xx;

}

class Program {

    public static void doAssert(boolean b)
        //@ requires b;
        //@ ensures true;
    {
        assert b;
    }

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Bar b = new Bar();
        Foo f = b;
        
        doAssert(f.x == 0);
        doAssert(f.y == 0);
        doAssert(f.z == 0);
        doAssert(f.o == null);
        doAssert(f.p == null);
        doAssert(b.xx == 0);
    }

}