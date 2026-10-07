// The generic proof of a function template constrained by std::integral does
// not cover bool. Templates that use their integral type parameters in ways
// the generic proof does not support are verified per instantiation.

#include <concepts>

// Verified once for every integer type other than bool. The specialization
// for bool is verified separately.
template <std::integral T>
T same(const T v)
//@ requires true;
//@ ensures result == v;
{
  return v;
}

// An operand of type int that is not a literal.
template <std::integral T>
T add(const T v, int n)
//@ requires 0 <= v && v < 10 && 0 <= n && n < 10;
//@ ensures result == v + n;
{
  return (T)(v + n);
}

// Bitwise operators depend on the width and signedness of T.
template <std::integral T>
T low_bit(const T v)
//@ requires 0 <= v && v < 10;
//@ ensures true;
{
  return (T)(v & 1);
}

// An implicit conversion back to T.
template <std::integral T>
T inc(const T v)
//@ requires v < 100;
//@ ensures result == v + 1;
{
  return v + 1;
}

int main()
//@ requires true;
//@ ensures true;
{
  int i = same(1);
  //@ assert i == 1;
  bool b = same(true);
  //@ assert b;
  long l = add(3L, 4);
  //@ assert l == 7;
  int z = low_bit(3);
  int w = inc(41);
  //@ assert w == 42;
  return 0;
}
