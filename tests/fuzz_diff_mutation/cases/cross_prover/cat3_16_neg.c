void frac_overclaim_neg(int *p)
//@ requires [1/2]*p |-> ?v;
//@ ensures *p |-> v; //~should_fail
{
}
