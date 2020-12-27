/*@

predicate foo(any x) = true;

inductive mybool = mytrue | myfalse;

lemma void ouch()
    requires true;
    ensures false;
{
    close foo(mytrue);
    close foo(myfalse);
    int x = 0;
    predicate(unit) p = foo;  //~ should_fail
    /*
    assert p(?u1) &*& p(?u2);
    switch (u1) {
        case unit:
            switch (u2) {
                case unit:
            }
    }
    */
}

@*/
