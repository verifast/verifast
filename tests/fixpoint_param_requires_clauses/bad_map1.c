/*@

fixpoint list<b> map1<a, b>(fixpoint(a x, b) requires x < xs f, list<a> xs) {
    switch (xs) {
        case nil: return cons(f(default_value), nil); //~should_fail
        case cons(h, t): return cons(f(h), map1(f, t));
    }
}

@*/
