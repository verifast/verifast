/*@

predicate call_perms_(int n, void *f;) =
    n == 0 ?
        emp
    :
        call_perm_(f) &*& call_perms_(n - 1, f);

lemma_auto void call_perm_weaken(int n, void *f)
    requires call_below_perm_(?f0) &*& func_lt(f, f0) == true;
    ensures call_perms_(n, f);
{
    assume(false);
}

@*/

typedef bool is_even_(int x);
    //@ requires 0 <= x &*& call_perms_(x / 2, is_even);
    //@ ensures true;
    //@ terminates;

bool is_odd(int x)
    //@ requires 0 <= x &*& call_perms_((x + 1) / 2, is_even);
    //@ ensures true;
    //@ terminates;
{
    //@ div_rem(x + 1, 2);
    if (x == 0) {
        return false;
    } else {
        is_even_ *is_even_ = is_even;
        //@ div_rem(x - 1, 2);
        return is_even_(x - 1);
    }
}

bool is_even(int x) //@ : is_even_
    //@ requires 0 <= x &*& call_perms_(x / 2, is_even);
    //@ ensures true;
    //@ terminates;
{
    //@ div_rem(x, 2);
    if (x == 0) {
        return true;
    } else {
        return is_odd(x - 1);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ assume(func_lt(is_even, main));
    ///@ call_perm_weaken(5, is_even);
    //@ div_rem(10, 2);
    is_even(10);
    return 0;
}