struct point {
  int x;
  int y;
};

struct point foo()
//@ requires true;
//@ ensures result.x == 1 && result.y == 2;
{
  struct point p = {1, 2};
  return p;
}

void test()
//@ requires true;
//@ ensures true;
{
  struct point p = foo();
  assert(p.x == 1 && p.y == 2);
}
