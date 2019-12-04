class MathImpl {
    static int ackermannIter(int m, int n)
        //@ requires 0 <= m &*& 0 <= n &*& call_perm_rec(currentThread, {MathImpl.class}, (pair_lt)(int_lt, int_lt), pair(m, n));
        //@ ensures 0 <= result;
        //@ terminates;
    {
        if (m == 0)
            return n + 1;
        if (n == 0) {
            //@ call_perm_rec_weaken(2, pair(m - 1, 1));
            //@ call_perm_rec_elim(1);
            //@ consume_call_perm_for(MathImpl.class);
            return ackermannIter(m - 1, 1);
        }
        //@ call_perm_rec_weaken(3, pair(m, n - 1));
        //@ call_perm_rec_elim(1);
        //@ consume_call_perm_for(MathImpl.class);
        int n1 = ackermannIter(m, n - 1);
        //@ call_perm_rec_weaken(2, pair(m - 1, n1));
        //@ call_perm_rec_elim(1);
        //@ consume_call_perm_for(MathImpl.class);
        return ackermannIter(m - 1, n1);
    }
}

public class Math {
    public static int ackermann(int m, int n)
        //@ requires 0 <= m &*& 0 <= n;
        //@ ensures true;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ is_wf_int_lt();
        //@ is_wf_pair_lt(int_lt, int_lt);
        //@ call_below_perm__elim_rec(1, {MathImpl.class}, (pair_lt)(int_lt, int_lt), pair(m, n));
        return MathImpl.ackermannIter(m, n);
    }
}
