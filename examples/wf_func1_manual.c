/*

fixpoint list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

*/

/*@

fixpoint list<int> range__def(fixpoint(int, int, list<int>) range, int min, int max) {
    return min == max ? nil : cons(min, range(min + 1, max));
}

inductive range__args = range__args(int min, int max);

fixpoint list<int> range__uncurry(fixpoint(range__args, list<int>) f, int min, int max) { return f(range__args(min, max)); }

fixpoint list<int> range__def_curried(fixpoint(range__args, list<int>) range, range__args args) {
    switch (args) {
        case range__args(min, max): return range__def((range__uncurry)(range), min, max);
    }
}

fixpoint int range__measure(range__args args) {
    switch (args) {
        case range__args(min, max): return max - min;
    }
}

fixpoint list<int> range(int min, int max) { return fix(range__def_curried, range__measure, range__args(min, max)); }

lemma void range_def(int min, int max)
    requires 0 <= max - min;
    ensures range(min, max) == (min == max ? nil : cons(min, range(min + 1, max)));
{
    if (range(min, max) != (min == max ? nil : cons(min, range(min + 1, max)))) {
        fix_unfold(range__def_curried, range__measure, range__args(min, max));
        open exists(pair(pair(?f1_, ?f2_), range__args(?min0, ?max0)));
        assert pair((range__uncurry)(f1_), (range__uncurry)(f2_)) == pair(?range1, ?range2); //~allow_dead_code
        // User code here
        assert range__def(range1, min0, max0) == range__def(range2, min0, max0); //~allow_dead_code
    }
}

@*/
