/*@

predicate foo(bool b) = true;

predicate bar(int *x, int *y) = foo(?b) &*& b ? *x |-> _ : *y |-> _;

lemma void merge_bar() // This lemma is false!
    requires [?f1]bar(?x, ?y) &*& [?f2]bar(x, y);
    ensures [f1 + f2]bar(x, y);
{
    assume(false);
}

@*/

int main()
    //@ requires true;
    //@ ensures true;
{
    int x, y;
    //@ close [1/2]foo(true);
    //@ close [1/2]bar(&x, &y);
    //@ close [1/2]foo(false);
    //@ close [1/2]bar(&x, &y);
    //@ merge_bar();
    //@ open bar(&x, &y);
    //@ assert foo(?b);
    //@ if (b) int__unique(&x); else int__unique(&y);
    assert(false);
}