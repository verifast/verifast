class Program {
    static int x;
    static void foo()
        //@ requires Program_x(?v);
        //@ ensures Program_x(v + 1);
    {
        Program.x = x + 1;
    }
}