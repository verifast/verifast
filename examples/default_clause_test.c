/*@

inductive foo = A | B | C | D;

fixpoint bool isA(foo f) {
    switch (f) {
        case A: return true;
        default: return false;
    }
}

fixpoint bool bothA(foo f1, foo f2) {
    switch (f1) {
        case A: return switch (f2) { case A: return true; default: return false; };
        default: return false;
    }
}

fixpoint bool eitherA(foo f1, foo f2) {
    switch (f1) {
        case A: return true;
        default: return switch (f2) { case A: return true; default: return false; };
    }
}

fixpoint bool allA(foo f1, foo f2, foo f3) {
    switch (f1) {
        case A: return switch (f2) { case A: return switch (f3) { case A: return true; default: return false; }; default: return false; };
        default: return false;
    }
}

fixpoint bool anyA(foo f1, foo f2, foo f3) {
    switch (f1) {
        case A: return true;
        default: return switch (f2) { case A: return true; default: return switch (f3) { case A: return true; default: return false; }; };
    }
}

lemma void test()
    requires true;
    ensures true;
{
    assert !!isA(A);
    assert !isA(B);
    assert !!bothA(A, A);
    assert !bothA(A, D);
    assert !bothA(C, A);
    assert !!eitherA(A, B);
    assert !!eitherA(D, A);
    assert !eitherA(B, D);
    assert !!allA(A, A, A);
    assert !allA(A, B, A);
    assert !allA(B, A, A);
    assert !allA(A, A, B);
    assert !allA(A, B, C);
    assert !!anyA(A, B, D);
    assert !!anyA(B, A, D);
    assert !!anyA(B, B, A);
    assert !anyA(B, C, C);
}

@*/