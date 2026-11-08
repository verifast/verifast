void heap_independent(int *p, int *q)
//@ requires *p |-> ?v &*& *q |-> ?w;
//@ ensures *p |-> 99 &*& *q |-> w;
{
    *p = 99;
}
