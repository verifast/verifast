/*@

fixpoint bool eq<t>(unit u, t x, t y) {
    switch (u) {
        case unit: return x == y;
    }
}

lemma_auto void unit_eq(unit x, unit y) //~ should_fail
    requires true;
    ensures eq(unit, x, y) == true;
{
    switch (x) {
        case unit:
        switch (y) {
            case unit:
        }
    }
}

inductive foo = foo1 | foo2;

lemma void eq_trans(bool b1, bool b2)
    requires b1 == true &*& b1 == b2;
    ensures b2;
{
}

@*/

int main()
    //@ requires true;
    //@ ensures false;
{
    //@ eq_trans(eq(unit, foo1, foo2), foo1 == foo2);
    assert(false);
}