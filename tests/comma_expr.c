void test()
//@ requires true;
//@ ensures true;
{
  int j = 0;
  for (int i = 0; (j++, i < 100); i++)
  //@ invariant i <= 100 &*& j == i;
  {}
}

int main()
//@ requires true;
//@ ensures true;
{
  int j = 0;
  for (int i = 0; j++, i < 100; i++)
  //@ invariant i <= 100 &*& j == i;
  {}

  return 0;
}
