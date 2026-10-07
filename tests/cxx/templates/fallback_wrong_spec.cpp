// A function template whose generic function does not type-check is verified
// per specialization, so errors in its specializations are still reported.

template <typename T>
T positive(const T x)
//@ requires x > 0;
//@ ensures result == x + 1; //~ should_fail
{
  return x;
}

int main()
//@ requires true;
//@ ensures true;
{
  int a = positive(3);
  return 0;
}
