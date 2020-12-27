/*@

lemma_auto void list_unit_eq(list<unit> xs, list<unit> ys) //~ should_fail
    requires true;
    ensures head(xs) == head(ys);
{
    switch (head<unit>(xs)) {
        case unit:
        switch (head<unit>(ys)) {
            case unit:
        }
    }
}

@*/

/*

inductive foo = foo1 | foo2;

lemma void eq_trans(foo f1, foo f2, foo f3)
    requires f1 == f2 &*& f2 == f3;
    ensures f1 == f3;
{
}

int main()
    //@ requires true;
    //@ ensures false;
{
    // assert head(cons(foo1, nil)) == head(cons(foo2, nil));
    assert(false);
}

*/
