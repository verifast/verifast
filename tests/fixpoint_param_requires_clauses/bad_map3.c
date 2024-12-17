/*@

fixpoint list<b> map1<a, b>(fixpoint(a x, b) requires x < xs f, list<a> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return map1(f, xs); //~should_fail
    }
}

@*/
