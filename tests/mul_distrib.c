/*@

fixpoint int mul(int x, int y) { return x * y; }

lemma void mul_distrib_test(int x, int y, int z)
    requires true;
    ensures mul(x, y + z) == x * y + x * z;
{}

@*/
