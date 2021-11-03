#define TEST1(x) x##01
#define TEST2(x) x##011
#define TEST3(x) x##0xa
#define TEST4(x) x##3UL

void test()
//@ requires true;
//@ ensures true;
{
  int N01 = 5;
  int N011 = 6;
  int N0xa = 7;
  int N3UL = 8;

  assert(TEST1(N) == 5);
  assert(TEST2(N) == 6);
  assert(TEST3(N) == 7);
  assert(TEST4(N) == 8);
} 
