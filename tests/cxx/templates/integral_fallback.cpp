// A function template constrained by std::integral whose generic function
// fails is verified per specialization instead, if something instantiates it.

#include <concepts>

// Does not verify generically: inc(150) does not fit in a signed char. But
// nothing instantiates it for signed char.
template <std::integral T>
T inc(const T v)
//@ requires 0 <= v && v < 200;
//@ ensures result == v + 1;
{
  return (T)(v + 1);
}

// Does not type-check generically: shifts of values of an integral type
// parameter are not supported, even in annotations.
template <std::integral T>
T twice(const T v)
//@ requires 0 <= v &*& v < 10 &*& (v << 1) < 100;
//@ ensures result == v + v;
{
  return (T)(v + v);
}

int main()
//@ requires true;
//@ ensures true;
{
  int i = inc(150);
  //@ assert i == 151;
  long l = inc(199L);
  //@ assert l == 200;
  int t = twice(6);
  //@ assert t == 12;
  return 0;
}
