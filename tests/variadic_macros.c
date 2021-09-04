int foo0()
//@ requires true;
//@ ensures result == 42;
{
  return 42;
}

int foo1(int x)
//@ requires true;
//@ ensures result == x;
{
  return x;
}

int foo2(int x, int y)
//@ requires INT_MIN <= x - y && x - y <= INT_MAX;
//@ ensures result == x - y;
{
  return x - y;
}

#define FOO(f, ...) f(__VA_ARGS__)
#define FOO2(...) foo2(__VA_ARGS__)

void test()
//@ requires true;
//@ ensures true;
{
  int result;
  result = FOO(foo0,);
  assert(result == 42);
  result = FOO(foo1, 10);
  assert(result == 10);
  result = FOO(foo2, 20, 30);
  assert(result == -10);
  result = FOO2(40, 60);
  assert(result == -20);
}
