int *return_null();
//@ requires true;
//@ ensures result == 0;

int unboxRef(int &i)
//@ requires *&i |-> ?v;
//@ ensures *&i |-> v &*& result == v;
{
  return i;
}

int main()
//@ requires true;
//@ ensures false;
{
  int i(4);
  //@ integer_limits(&i);
  int i_val = unboxRef(i);
  //@ assert i_val == 4;

  int *n = return_null();
  unboxRef(*n); //~ should_fail
}