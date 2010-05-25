/*@

lemma_auto void map_unit_lemma(fixpoint(int, unit) f, int x, fixpoint(int, unit) g, int y) //~ should_fail
    requires true;
    ensures f(x) == g(y);
{
    switch (f(x)) {
        case unit:
    }
    switch (g(y)) {
        case unit:
    }
}

fixpoint int id(unit u, int x) {
    switch (u) {
        case unit: return x;
    }
}

lemma void eq_trans(int x, int y, int z)
    requires x == y &*& y == z;
    ensures x == z;
{
}

@*/

int main()
    //@ requires true;
    //@ ensures false;
{
    //@ fixpoint(int, int) f = (id)(unit);
    //@ int X = f(1);
    //@ int Y = f(2);
    //@ assert X == Y;
    //@ assert X == 1;
    //@ assert Y == 2;
    //@ assert X == 1 && Y == 2;
    //@ assert X == id(unit, 1);
    //@ assert Y == id(unit, 2);
    //@ eq_trans(1, X, Y);
    //@ eq_trans(1, Y, 2);
    assert(false);
}