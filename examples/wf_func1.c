/*@

fixpoint_auto list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + sum(xs0);
    }
}

@*/

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    while (count != n)
    //@ requires 0 <= count && count <= n;
    //@ ensures sum == old_sum + sum(range(old_count, n));
    //@ decreases n - count;
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}
