int main()
//@ requires true;
//@ ensures true;
{
  int a = 5, b = 7;
  int one = a < b;
  assert(one == 1);
  int zero = b < a;
  assert(zero == 0);
  return 0;
}
