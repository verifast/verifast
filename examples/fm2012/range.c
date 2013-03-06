// implementation of range.gh
//@ #include "nat.gh"

/*@
fixpoint list<int> range_diff(int x, nat diff) {
  switch(diff) {
    case zero: return nil;
    case succ(diff0): return cons(x, range_diff(x + 1, diff0));
  }
}

fixpoint list<int> range(int x, int y) {
  return 0 <= x && x <= y ? range_diff(x, nat_of_int(y - x)) : nil;
}

lemma void range_empty(int x)
  requires true;
  ensures range(x, x) == nil;
{
}

lemma void mem_range_diff(int x, nat diff, int z)
  requires 0 <= x;
  ensures mem(z, range_diff(x, diff)) == (x <= z && z < x + int_of_nat(diff));
{
  switch(diff) {
    case zero:
    case succ(diff0): mem_range_diff(x + 1, diff0, z);
  }
}

lemma void mem_range(int x, int y, int z)
  requires 0 <= x && x <= y;
  ensures mem(z, range(x, y)) == (x <= z && z < y);
{
  mem_range_diff(x, nat_of_int(y - x), z);
}
@*/