int frac_read(int *p)
//@ requires [1/2]*p |-> ?v;
//@ ensures [1/2]*p |-> v &*& result == v;
{
    return *p;
}
