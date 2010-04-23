/*@

inductive baz = baz(fixpoint(baz, int));  //~ should_fail

fixpoint int quux(baz b) {
    switch (b) {
        case baz(f): return f(b) + 1;
    }
}

lemma void ouch()
    requires true;
    ensures false;
{
    assert quux(baz(quux)) == quux(baz(quux)) + 1;
}

@*/
