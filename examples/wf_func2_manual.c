/*

fixpoint list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

*/

/*@

fixpoint list<t> n_times__def<t>(fixpoint(t, int, list<t>) n_times, t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

inductive n_times__args<t> = n_times__args(t x, int count);

fixpoint list<t> n_times__uncurry<t>(fixpoint(n_times__args<t>, list<t>) n_times, t x, int count) {
    return n_times(n_times__args(x, count));
}

fixpoint list<t> n_times__def_curried<t>(fixpoint(n_times__args<t>, list<t>) n_times, n_times__args<t> args) {
    switch (args) {
        case n_times__args(x, count): return n_times__def((n_times__uncurry)(n_times), x, count);
    }
}

fixpoint int n_times__measure<t>(n_times__args<t> args) {
    switch (args) {
        case n_times__args(x, count): return count;
    }
}

fixpoint list<t> n_times<t>(t x, int count) { return fix(n_times__def_curried, n_times__measure, n_times__args(x, count)); }

lemma void n_times_def<t>(t x, int count)
    requires 0 <= count;
    ensures n_times(x, count) == (count == 0 ? nil : cons(x, n_times(x, count - 1)));
{
    if (n_times(x, count) != (count == 0 ? nil : cons(x, n_times(x, count - 1)))) {
        fix_unfold(n_times__def_curried, n_times__measure, n_times__args(x, count));
        open exists(pair(pair(?f1_, ?f2_), n_times__args(?x0, ?count0)));
        assert pair((n_times__uncurry)(f1_), (n_times__uncurry)(f2_)) == pair(?n_times1, ?n_times2); //~allow_dead_code
        // User code here
        assert n_times__def(n_times1, x0, count0) == n_times__def(n_times2, x0, count0); //~allow_dead_code
    }
}

@*/


