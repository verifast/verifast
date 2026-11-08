//@ predicate cell(int *p; int v) = *p |-> v;
void pred_frac_write_neg(int *p)
//@ requires [1/2]cell(p, ?v);
//@ ensures [1/2]cell(p, ?w);
{
    *p = 1; //~should_fail
}
