/*@

inductive list = nil | cons(int, list);

fixpoint list sum(list l1, list l2) {
    switch (l1) {
        case nil: return nil;
        case cons(h1, t1):
            return
                switch (l2) {
                    case nil: return nil;
                    case cons(h2, t2): return cons(h1 + h2, sum(t1, t2));
                };
    }
}

lemma void test()
    requires emp;
    ensures emp;
{
    assert cons(111, cons(222, cons(33, nil))) == sum(cons(101, cons(202, cons(303, nil))), cons(10, cons(20, cons(30, nil))));
}

@*/