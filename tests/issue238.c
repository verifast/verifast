bool test(int x, int y)
//@ requires true;
//@ ensures result == (y < 0 && x < 0);
{
  return x < 0 && y < 0;
}
