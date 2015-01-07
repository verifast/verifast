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

//Iterative proof (and helper lemmas) for the same lemma
lemma void int_of_nat_injective(nat m, nat n)
  requires int_of_nat(m) == int_of_nat(n);
  ensures  m == n;
{
  int i0 = 0;
  nat n0 = zero;
  
  while (i0 < int_of_nat(m))
    invariant 0 <= i0 && i0 <= int_of_nat(m) &*&
              n0 == nat_of_int(i0);
    decreases int_of_nat(m) - i0;
  {
    i0 = i0 + 1;
    n0 = succ(n0);
  }
}

lemma void check_equal_iterative_base1(nat m)
  requires true;
  ensures  sum_left(m, zero) == sum_right(m, zero);
{
  nat i = zero;
  while (int_of_nat(i) < int_of_nat(m))
    invariant 0 <= int_of_nat(i) && int_of_nat(i) <= int_of_nat(m) &*&
              sum_left(i, zero) == sum_right(i, zero);
    decreases int_of_nat(m) - int_of_nat(i);
  {
    i = succ(i);
  }
  int_of_nat_injective(i, m); 
}

lemma void check_equal_iterative_base2(nat n)
  requires true;
  ensures  sum_left(zero, n) == sum_right(zero, n);
{
  nat j = zero;
  while (int_of_nat(j) < int_of_nat(n))
    invariant 0 <= int_of_nat(j) && int_of_nat(j) <= int_of_nat(n) &*&
              sum_left(zero, j) == sum_right(zero, j);
    decreases int_of_nat(n) - int_of_nat(j);
  {
    j = succ(j);
  }
  int_of_nat_injective(j, n); 
}

fixpoint bool proven_facts(nat m, nat n)
{
  switch(n)
  {
    case succ(n0):
      return sum_left(m, n) == sum_right(m, n) &&
             proven_facts(m, n0);
    case zero:
      return sum_left(m, n) == sum_right(m, n);
  }
}

lemma void extract_proven_facts(nat m, nat n, nat i)
  requires true == proven_facts(m, n) &&
           int_of_nat(i) <= int_of_nat(n);
  ensures  sum_left(m, i) == sum_right(m, i);
{
  nat i0 = n;
  
  while(int_of_nat(i0) > int_of_nat(i))
    invariant int_of_nat(i) <= int_of_nat(i0) && 
              int_of_nat(i0) <= int_of_nat(n) &*&
              true == proven_facts(m, i0);
    decreases int_of_nat(i0);
  {
    switch(i0)
    {
      case zero:
      case succ(i1):
        i0 = i1;
    }
  }
  
  int_of_nat_injective(i, i0);
  switch(i){case zero: case succ(i1):}
}

lemma void check_equal_iterative(nat m, nat n)
  requires true;
  ensures  sum_left(m, n) == sum_right(m, n);
{
  nat i = zero;
  nat i_prev = zero;
  
  while (int_of_nat(i) < int_of_nat(succ(m)))
    invariant 0 <= int_of_nat(i) &*& 
              int_of_nat(i) <= int_of_nat(succ(m)) &*&
              i == zero ?
                true
              :
                i == succ(i_prev) && proven_facts(i_prev, n);
    decreases (int_of_nat(succ(m)) - int_of_nat(i));
  {
    nat j = zero;
    nat j_prev = zero;
  
    while (int_of_nat(j) < int_of_nat(succ(n)))
      invariant 0 <= int_of_nat(j) &*& 
                int_of_nat(j) <= int_of_nat(succ(n)) &*&
                j == zero ?
                  true
                :
                  j == succ(j_prev) && proven_facts(i, j_prev);
      decreases (int_of_nat(succ(n)) - int_of_nat(j));
    {
      if (j == zero)
      {
        check_equal_iterative_base1(i);
      }
      else
      {
        if (i == zero)
        {
          check_equal_iterative_base2(j);
        }
        else
        { 
          extract_proven_facts(i, j_prev, j_prev);
          extract_proven_facts(i_prev, n, j);
          extract_proven_facts(i_prev, n, j_prev);
          assert sum_left(i, j) == sum_right(i, j);
        }
      }
      
      j_prev = j;
      j = succ(j);
    }
    
    int_of_nat_injective(j, succ(n));
    assert j == succ(n);
    assert j_prev == n;
    
    i_prev = i;
    i = succ(i);
  }
  
  int_of_nat_injective(i, succ(m));
  switch(n) {case zero: case succ(n0):}
}

@*/









