/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint int length<t>(list<t> xs) {
    switch (xs) {
         case nil: return 0;
         case cons(x, xs0): return 1 + length(xs0);
    }
}

fixpoint list<t> append<t>(list<t> l1, list<t> l2) {
    switch (l1) {
        case nil: return l2;
        case cons(x, xs): return cons(x, append(xs, l2));
    }
}

fixpoint bool le(list<int> l1, list<int> l2) {
    switch (l1) {
        case nil: return true;
        case cons(x, xs):
            return
                switch (l2) {
                    case nil: return false;
                    case cons(y, ys): return x <= y && le(xs, ys);
                };
    }
}

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + sum(xs0);
    }
}

lemma void foo(list<int> l)
    requires l == cons(10, cons(20, nil));
    ensures sum(l) == 30;
{
    assert le(cons(5, cons(7, nil)), cons(10, cons(100, cons(1000, nil)))) == true;
    assert length(l) == 2;
    assert length(append(l, l)) == 4;
}

lemma void length_nonnegative<t>(list<t> xs)
    requires true;
    ensures 0 <= length(xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
    }
}

predicate int_array(int *p, list<int> elements)
    requires
        switch (elements) {
            case nil: return emp;
            case cons(x, xs): return integer(p, x) &*& int_array(p + 1, xs);
        };

lemma void pair_to_array(int *p0)
    requires integer(p0, ?v0) &*& integer(p0 + 1, ?v1);
    ensures int_array(p0, cons(v0, cons(v1, nil)));
{
    close int_array(p0 + 2, nil);
    close int_array(p0 + 1, cons(v1, nil));
    close int_array(p0, cons(v0, cons(v1, nil)));
}

@*/
