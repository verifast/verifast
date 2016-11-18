//@ #include <nat.gh>
//@ #include "termination.gh"

/*@

fixpoint nat Am(fixpoint(nat, nat) Am1, nat n) {
    switch (n) {
        case zero: return Am1(succ(zero));
        case succ(n0): return Am1(Am(Am1, n0));
    }
}

fixpoint nat A(nat m, nat n) {
    switch (m) {
        case zero: return succ(n);
        case succ(m1): return Am((A)(m1), n);
    }
}

@*/

// TODO: Support recursive calls directly.
// Workaround: Perform the recursive calls as function pointer calls.

typedef int ackermann_iter_(int m, int n);
    //@ requires 0 <= m &*& 0 <= n &*& [2]call_perm_level(pair((pair_lt)(lt, lt), pair(m, n)), {ackermann_iter});
    //@ ensures result == int_of_nat((A)(nat_of_int(m))(nat_of_int(n)));
    //@ terminates;

int ackermann_iter(int m, int n) //@ : ackermann_iter_
    //@ requires 0 <= m &*& 0 <= n &*& [2]call_perm_level(pair((pair_lt)(lt, lt), pair(m, n)), {ackermann_iter});
    //@ ensures result == int_of_nat((A)(nat_of_int(m))(nat_of_int(n)));
    //@ terminates;
{
    ackermann_iter_ *ackermann_iter_ = ackermann_iter;
    if (m == 0) {
        //@ leak [2]call_perm_level(pair((pair_lt)(lt, lt), pair(m, n)), {ackermann_iter});
        return n + 1;
    } else {
        //@ succ_int(m - 1);
        if (n == 0) {
            //@ is_wf_lt();
            //@ is_wf_pair_lt(lt, lt);
            //@ call_perm_level_weaken(2, (pair_lt)(lt, lt), pair(m, n), {ackermann_iter}, 3, pair(m - 1, 1));
            //@ consume_call_perm_level_for(ackermann_iter);
            int r = ackermann_iter_(m - 1, 1);
            return r;
        } else {
            //@ is_wf_lt();
            //@ is_wf_pair_lt(lt, lt);
            //@ call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(m, n), {ackermann_iter}, 3, pair(m, n - 1));
            //@ succ_int(n - 1);
            //@ consume_call_perm_level_for(ackermann_iter);
            int r1 = ackermann_iter_(m, n - 1);
            //@ call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(m, n), {ackermann_iter}, 3, pair(m - 1, r1));
            //@ consume_call_perm_level_for(ackermann_iter);
            int r2 = ackermann_iter_(m - 1, r1);
            return r2;
        }
    }
}

int ackermann(int m, int n)
    //@ requires 0 <= m &*& 0 <= n;
    //@ ensures result == int_of_nat((A)(nat_of_int(m))(nat_of_int(n)));
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(ackermann);
    //@ call_perm_level(2, pair((pair_lt)(lt, lt), pair(m, n)), {ackermann_iter});
    return ackermann_iter(m, n);
}