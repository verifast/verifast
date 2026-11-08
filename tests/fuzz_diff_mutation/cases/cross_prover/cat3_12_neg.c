//@ predicate cell(int *p; int v) = *p |-> v;
void pred_not_held_neg(int *p)
//@ requires true;
//@ ensures true;
{
    //@ open cell(p, _); //~should_fail
}
