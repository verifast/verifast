/*@

predicate int_array(int *xs, int n)
    requires
        0 <= n &*& n == 0 ? emp : integer(xs, _) &*& int_array(xs + 1, n - 1);

lemma void split(int *xs, int offset);
    requires int_array(xs, ?n) &*& 0 <= offset &*& offset <= n;
    ensures int_array(xs, offset) &*& int_array(xs + offset, n - offset);

lemma void merge(int *xs);
    requires int_array(xs, ?n) &*& int_array(xs + n, ?m);
    ensures int_array(xs, n + m);

@*/

void quicksort(int n, int *xs)
    //@ requires int_array(xs, n);
    //@ ensures int_array(xs, n);
{
    if (2 <= n) {
        //@ open int_array(xs, n);
        int pivot = *xs;
        //@ close int_array(xs, n);
        int l = 0;
        int r = n;
        while (l < r)
            /*@ invariant
                    0 <= l &*& l <= r &*& r <= n &*&
                    int_array(xs, n);
              @*/
        {
            //@ split(xs, r - 1);
            //@ open int_array(xs + r - 1, n - (r - 1));
            int b = *(xs + r - 1);
            //@ close int_array(xs + r - 1, n - (r - 1));
            //@ merge(xs);
            if (b < pivot) {
                //@ split(xs, l);
                //@ open int_array(xs + l, n - l);
                int a = *(xs + l);
                //@ close int_array(xs + l, n - l);
                //@ merge(xs);
                //@ split(xs, r - 1);
                //@ open int_array(xs + r - 1, n - (r - 1));
                *(xs + r - 1) = a;
                //@ close int_array(xs + r - 1, n - (r - 1));
                //@ merge(xs);
                //@ split(xs, l);
                //@ open int_array(xs + l, n - l);
                *(xs + l) = b;
                //@ close int_array(xs + l, n - l);
                //@ merge(xs);
                l = l + 1;
            } else {
                r = r - 1;
            }
        }
        //@ split(xs, l);
        quicksort(l, xs);
        quicksort(n - l, xs + l);
        //@ merge(xs);
    }
}