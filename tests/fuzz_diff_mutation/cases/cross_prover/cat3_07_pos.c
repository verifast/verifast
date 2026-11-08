void heap_disjoint(int *p, int *q)
//@ requires *p |-> ?v &*& *q |-> ?w;
//@ ensures *p |-> v &*& *q |-> w &*& p != q;
{
    //@ integer_distinct(p, q);
}
