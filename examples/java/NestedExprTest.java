class Test {
    int x;

    Test()
        //@ requires true;
        //@ ensures x |-> 0;
    {
    }

    int foo(int a)
        //@ requires x |-> ?v &*& v == a;
        //@ ensures x |-> v + 1 &*& result == v + 1;
    {
        x++;
        return x;
    }

    static void bar(int a, int b)
        //@ requires a == 1 &*& b == 2;
        //@ ensures true;
    {
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        Test t = new Test();
        bar(t.foo(0), t.foo(1));
        //@ assert t.x |-> 2;
    }
}