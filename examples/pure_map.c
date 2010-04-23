/*@

inductive color = red | black;

fixpoint color flip(color c) {
    switch (c) {
        case red: return black;
        case black: return red;
    }
}

lemma void test()
    requires true;
    ensures map(flip, cons(red, cons(black, nil))) == cons(black, cons(red, nil));
{
}

@*/