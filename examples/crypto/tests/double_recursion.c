//@ #include "nat.gh"

/*@

//==============================================================================
// sum_left ====================================================================
//==============================================================================

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

lemma void check_sum_left()
  requires true;
  ensures true;
{
  assert sum_left(zero, zero) == zero;
  assert sum_left(succ(zero), zero) == succ(zero);
  assert sum_left(zero, succ(zero)) == succ(zero);
  assert sum_left(succ(zero), succ(zero)) == succ(succ(zero));
  assert sum_left(succ(zero), succ(succ(zero))) == succ(succ(succ(zero)));
  assert sum_left(succ(succ(zero)), succ(zero)) == succ(succ(succ(zero)));
  assert sum_left(succ(succ(zero)), succ(succ(zero))) ==
         succ(succ(succ(succ(zero))));
}

//==============================================================================
// sum_right ===================================================================
//==============================================================================

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

lemma void check_sum_right()
  requires true;
  ensures true;
{
  assert sum_right(zero, zero) == zero;
  assert sum_right(succ(zero), zero) == succ(zero);
  assert sum_right(zero, succ(zero)) == succ(zero);
  assert sum_right(succ(zero), succ(zero)) == succ(succ(zero));
  assert sum_right(succ(zero), succ(succ(zero))) == succ(succ(succ(zero)));
  assert sum_right(succ(succ(zero)), succ(zero)) == succ(succ(succ(zero)));
  assert sum_right(succ(succ(zero)), succ(succ(zero))) ==
         succ(succ(succ(succ(zero))));
}

//==============================================================================
// sum_zero ====================================================================
//==============================================================================

lemma void sum_zero(nat n)
  requires true;
  ensures  sum_left(zero, n) == n &&
           sum_left(n, zero) == n &&
           sum_right(zero, n) == n &&
           sum_right(n, zero) == n;
{
  switch(n)
  {
    case succ(n0):
      sum_zero(n0);
    case zero:
  }
}

//==============================================================================
// check_equal_switch_args =====================================================
//==============================================================================

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

//==============================================================================
// check_equal_nested ==========================================================
//==============================================================================

lemma void check_equal_nested_base(nat n)
  requires true;
  ensures  sum_left(zero, n) == sum_right(zero, n);
{
  switch(n)
  {
    case succ(n0):
      check_equal_nested_base(n0);
    case zero:
  }
}

lemma void check_equal_nested(nat m, nat n)
  requires true;
  ensures  sum_left(m, n) == sum_right(m, n);
{
  switch(m)
  {
    case succ(m0):
      {
        lemma void check_equal_nested_inductive(nat m_, nat n_)
          requires true;
          ensures  sum_left(succ(m_), n_) == sum_right(succ(m_), n_);
        {
          check_equal_nested(succ(m_), n_);
        }
        check_equal_nested_inductive(m0, n);
      }
    case zero:
      check_equal_nested_base(n);
  }
}

//==============================================================================
//==============================================================================
//==============================================================================

@*/