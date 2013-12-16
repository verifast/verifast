//@ #include "nat.gh"
//@ #include "range.gh"

/*@

lemma void mem_range_(int start, nat count, int x)
  requires true;
  ensures mem(x, range_(start, count)) == (start <= x && x < start + int_of_nat(count));
{
  switch (count) {
    case zero:
    case succ(count0): mem_range_(start + 1, count0, x);
  }
}

lemma void mem_range(int x, int y, int z)
  requires true;
  ensures mem(z, range(x, y)) == (x <= z && z < y);
{
  mem_range_(x, nat_of_int(y - x), z);
  if (x <= y) {
    assert mem(z, range(x, y)) == mem(z, range_(x, nat_of_int(y - x)));
    int_of_nat_of_int(y - x);
    assert y == x + int_of_nat(nat_of_int(y - x));
  } else {
  }
}

@*/