class Program {
    static int x;
    static void foo()
        //@ requires x |-> ?v;
        //@ ensures x |-> v + 1;
    {
        x = x + 1;
    }
}