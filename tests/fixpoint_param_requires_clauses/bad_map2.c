/*@

fixpoint list<b> map0<a, b>(fixpoint(a x, b) f, list<a> xs) {
    switch (xs) {
        case nil: return cons(f(default_value), nil);
        case cons(h, t): return cons(f(h), map(f, t));
    }
}

fixpoint list<b> map1<a, b>(fixpoint(a x, b) requires x < xs f, list<a> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return cons(f(h), map0(f, t)); //~should_fail
    }
}

@*/
