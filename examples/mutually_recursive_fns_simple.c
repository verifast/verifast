/*@
fixpoint bool is_odd(int x);
fixpoint bool is_even(int x);

lemma_auto void is_odd_def(int x);
  requires 0 <= x;
  ensures is_odd(x) == (x != 0 && is_even(x - 1));

lemma_auto void is_even_def(int x);
  requires 0 <= x;
  ensures is_even(x) == (x == 0 || is_odd(x - 1));
@*/

bool is_even_nat(int x)
//@ requires 0 <= x;
//@ ensures result == is_even(x);
{
  if(x == 0)
    return true;
  else if(x == 1)
    return false;
  else {
    // case split
    //@ if(x < 0) {} else {}
    //@ if(x < 1) {} else {}
    return is_even_nat(x - 2);
  }
}