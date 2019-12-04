/*@

predicate call_perms_(int thread, int n, void *f;) =
    n == 0 ?
        emp
    :
        1 <= n &*&
        call_perm_(thread, f) &*& call_perms_(thread, n - 1, f);

lemma_auto void call_perm_weaken(int n, void *f)
    requires call_below_perm_(?thread, ?f0) &*& func_lt(f, f0) == true;
    ensures call_perms_(thread, n, f);
{
    assume(false);
}

@*/

typedef bool is_even_(int x);
    //@ requires exists<int>(?n) &*& 0 <= x &*& x == 2 * n || x == 2 * n + 1 &*& call_perms_(currentThread, n, is_even);
    //@ ensures true;
    //@ terminates;

bool is_odd(int x)
    //@ requires exists<int>(?n) &*& 0 <= x &*& x == 2 * n || x == 2 * n - 1 &*& call_perms_(currentThread, n, is_even);
    //@ ensures true;
    //@ terminates;
{
    //@ open exists(n);
    //@ open call_perms_(currentThread, n, is_even);
    if (x == 0) {
        return false;
    } else {
        is_even_ *is_even_ = is_even;
        //@ close exists(n - 1);
        return is_even_(x - 1);
    }
}

bool is_even(int x) //@ : is_even_
    //@ requires exists<int>(?n) &*& 0 <= x &*& x == 2 * n || x == 2 * n + 1 &*& call_perms_(currentThread, n, is_even);
    //@ ensures true;
    //@ terminates;
{
    //@ open exists(n);
    //@ open call_perms_(currentThread, n, is_even);
    if (x == 0) {
        return true;
    } else {
        //@ close exists(n);
        return is_odd(x - 1);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ close exists(5);
    is_even(10);
    return 0;
}