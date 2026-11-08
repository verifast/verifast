//@ predicate cell(int *p; int v) = *p |-> v;
void pred_mod(int *p)
//@ requires cell(p, ?v);
//@ ensures cell(p, v + 1);
{
    //@ open cell(p, v);
    *p = *p + 1;
    //@ close cell(p, v + 1);
}
