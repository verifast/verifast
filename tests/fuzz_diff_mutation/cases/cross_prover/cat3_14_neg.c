void heap_alias_neg(int *p, int *q)
//@ requires *p |-> ?v &*& *q |-> ?w;
//@ ensures p == q; //~should_fail
{
}
