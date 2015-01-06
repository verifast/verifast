//@ #include "nat.gh"

/*@

fixpoint nat sum_left(nat m, nat n)
{
  switch(m)
  {
    case succ(m0):
      return succ(sum_left(m0, n));
    case zero:
      return n;
  }
}

fixpoint nat sum_right(nat m, nat n)
{
  switch(n)
  {
    case succ(n0):
      return succ(sum_right(m, n0));
    case zero:
      return m;
  }
}

lemma void check_equal_switch_args(nat m, nat n)
  requires true;
  ensures  sum_left(m, n) == sum_right(n, m);
{
  switch(m)
  {
    case succ(m0):
      check_equal_switch_args(m0, n);
    case zero:
  }
}

lemma void check_equal_double_recursion_base1(nat m)
  requires true;
  ensures  sum_left(m, zero) == sum_right(m, zero);
{
  switch(m)
  {
    case succ(m0):
      check_equal_double_recursion_base1(m0);
    case zero:
  }
}

lemma void check_equal_double_recursion_base2(nat n)
  requires true;
  ensures  sum_left(zero, n) == sum_right(zero, n);
{
  switch(n)
  {
    case succ(n0):
      check_equal_double_recursion_base2(n0);
    case zero:
  }
}

lemma void check_equal_double_recursion(nat m, nat n)
  requires true;
  ensures  sum_left(m, n) == sum_right(m, n);
{
  switch(m)
  {
    case succ(m0):
      switch(n)
      {
        case succ(n0):
          check_equal_double_recursion(m0, n);
          check_equal_double_recursion(m0, n0);
          check_equal_double_recursion(m, n0);
        case zero:
          check_equal_double_recursion_base1(m);
      }
    case zero:
      check_equal_double_recursion_base2(n);
  }
}

@*/