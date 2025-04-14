/*@

fixpoint boolean increasing_from(int lower, list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return lower <= x0 && increasing_from(x0 + 1, xs0);
    }
}

fixpoint boolean increasing(list<int> xs) {
    return increasing_from(Integer.MIN_VALUE, xs);
}

fixpoint list<t> filter<t>(fixpoint(t, boolean) f, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return f(x0) ? cons(x0, filter(f, xs0)) : filter(f, xs0);
    }
}

fixpoint boolean contains<t>(list<t> xs, t x) { return mem(x, xs); }

lemma void filter_contains_nil<t>(list<t> xs)
    requires true;
    ensures filter((contains)(nil), xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            filter_contains_nil(xs0);
    }
}

lemma void increasing_lt_contains(int x, list<int> xs, int y)
    requires increasing(cons(x, xs)) && y < x;
    ensures !mem(y, cons(x, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            increasing_lt_contains(x0, xs0, y);
    }
}

lemma void filter_contains_lt(int x, list<int> xs, int y, list<int> ys)
    requires y < x && increasing(cons(x, xs)) && increasing(cons(y, ys));
    ensures filter((contains)(ys), cons(x, xs)) == filter((contains)(cons(y, ys)), cons(x, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            filter_contains_lt(x0, xs0, y, ys);
    }
}

@*/

class CoincidenceCount {

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs[..] |-> ?as &*& ys[..] |-> ?bs &*& increasing(as) && increasing(bs);
	//@ ensures xs[..] |-> as &*& ys[..] |-> bs &*& result == length(filter((contains)(bs), as));
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ requires xs[i..] |-> ?as1 &*& ys[j..] |-> ?bs1 &*& increasing(as1) && increasing(bs1) &*& n <= i;
		//@ ensures xs[old_i..] |-> as1 &*& ys[old_j..] |-> bs1 &*& n == old_n + length(filter((contains)(bs1), as1));
		{
		    //@ switch (as1) { case nil: case cons(h, t): }
			if (i == xs.length) {
				break;
			}
			//@ assert as1 == cons(?x, ?as10);
		    //@ switch (bs1) { case nil: case cons(h, t): }
			if (j == ys.length) {
			    //@ filter_contains_nil(as1);
				break;
			}
			//@ assert bs1 == cons(?y, ?bs10);
    	    //@ switch (as10) { case nil: case cons(h, t): }
		    //@ switch (bs10) { case nil: case cons(h, t): }
			if (xs[i] < ys[j]) {
			    //@ increasing_lt_contains(y, bs10, x);
			    //@ assert !contains(bs1, x);
				i++;
			} else if (xs[i] > ys[j]) {
			    //@ filter_contains_lt(x, as10, y, bs10);
				j++;
			} else {
				n++;
				i++;
				j++;
				/*@
				switch (as10) {
				    case nil:
				    case cons(x0, as100):
				        filter_contains_lt(x0, as100, y, bs10);
				}
				@*/
			}
		}
		return n;
	}
}
