void frac_write_neg(int *p)
//@ requires [1/2]*p |-> ?v;
//@ ensures [1/2]*p |-> 10;
{
    *p = 10; //~should_fail
}
