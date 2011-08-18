class InitTest {
    static void test2()
        //@ requires true;
        //@ ensures true;
    {
        int[] xs = new int[100];
        //@ assert array_slice(xs, 0, 100, ?elems);
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    static void test3(int[] xs)
        //@ requires array_slice(xs, 60, 70, ?elems) &*& all_eq(elems, 0) == true;
        //@ ensures true;
    {
    }
}
