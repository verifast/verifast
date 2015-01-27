class Program {
    static int x;
    static void foo()
        //@ requires x |-> ?v;
        //@ ensures x |-> v + 1;
    {
        x = x + 1;
    }
    
    static int[] y = {1,2,3,4};
    public static void main(String[] args)
        //@ requires class_init_token(Program.class);
        //@ ensures true;
    {
        //@ init_class(Program.class);
        foo();
        assertEq(x, 1);
        assertEq(y.length, 4);
        assertEq(y[0], 1);
        assertEq(y[1], 2);
        assertEq(y[2], 3);
        assertEq(y[3], 4);
    }
    
    static void assertEq(int expected, int actual)
        //@ requires expected == actual;
        //@ ensures true;
    {
        assert(expected == actual);
    }
    
    //@ predicate foo(int v) = Program.x |-> v &*& x |-> v;
}