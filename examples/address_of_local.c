void inc(int* i)
  //@ requires integer(i, ?v);
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}

void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    x = 5;
    int* ptr = &x; 
    inc(ptr);
    int z = x;
    assert(z == 6);
}

void address_of_local() 
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  {
    int* ptr = &x;
    {
      int** ptrptr = &ptr;
      inc(*ptrptr);
      int z = x;
      assert(z == 1);
    }
  }
}

void destroy(int* i) 
  //@ requires integer(i, _);
  //@ ensures true;
{
  //@ assume(false);
}

void dispose_local() //~ should_fail
  //@ requires true;
  //@ ensures true;
{
  int x = 0;
  destroy(&x);
}