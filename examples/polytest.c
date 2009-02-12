/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint int length(list<boxed_int> xs) {
    switch (xs) {
         case nil: return 0;
         case cons(x, xs0): return 1 + length(xs0);
    }
}

fixpoint int sum(list<boxed_int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return unboxed_int(x) + sum(xs0);
    }
}

lemma void foo(list<boxed_int> l)
    requires l == cons<boxed_int>(boxed_int(10), cons<boxed_int>(boxed_int(20), nil<boxed_int>));
    ensures sum(l) == 30;
{
}

@*/
