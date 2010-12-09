#ifndef NAT_H
#define NAT_H

/*@

inductive nat = zero | succ(nat);

fixpoint int int_of_nat(nat n) {
    switch (n) {
        case zero: return 0;
        case succ(n0): return 1 + int_of_nat(n0);
    }
}

fixpoint nat nat_of_int(int n);

lemma void int_of_nat_of_int(int n);
    requires 0 <= n;
    ensures int_of_nat(nat_of_int(n)) == n;

lemma_auto void int_of_nat_nonnegative(nat n);
    requires true;
    ensures 0 <= int_of_nat(n);

@*/

#endif