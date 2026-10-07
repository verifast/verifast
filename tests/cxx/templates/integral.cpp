// A function template whose type parameter T is constrained by std::integral
// is verified once, for every integer type other than bool. In that proof, T
// is an integer type with unknown limits. The body can do arithmetic on values
// of type T, which the integer promotions convert to an unknown type of at
// least the rank of int.

#include <concepts>
#include <stdint.h>

template <std::integral T>
T clamp100(const T v)
//@ requires true;
//@ ensures v <= 100 ? result == v : result == 100;
{
  if (v > 100 && v != 0) {
    // Every type argument can represent 100.
    return (T)100;
  }
  return v;
}

template <std::integral T>
T dec(const T v)
//@ requires v > 0;
//@ ensures result == v - 1;
{
  return (T)(v - 1);
}

template <std::integral T>
T count_to(const T n)
//@ requires 0 <= n;
//@ ensures result == n;
{
  T i = (T)0;
  while (i < n)
  //@ invariant 0 <= i && i <= n;
  {
    i = (T)(i + 1);
  }
  return i;
}

template <std::integral T>
bool is_digit(const T v)
//@ requires true;
//@ ensures result == (0 <= v && v < 10);
{
  bool b = !(v < 0) && v < 10;
  return b;
}

template <std::integral T, std::integral U>
U convert(const T v)
//@ requires 0 <= v && v < 100;
//@ ensures result == v;
{
  return static_cast<U>(v);
}

// The requires-clause form of the constraint.
template <typename T>
  requires std::integral<T>
T twice(const T v)
//@ requires 0 <= v && v < 50;
//@ ensures result == 2 * v;
{
  //@ T g = v;
  return (T)(v * 2);
}

template <std::integral T>
T declared_first(const T v);
//@ requires v < 50;
//@ ensures result == v + 1;

template <std::integral T>
T declared_first(const T v)
//@ requires v < 50;
//@ ensures result == v + 1;
{
  return (T)(1 + v);
}

// Only T is constrained. U is verified as any scalar type.
template <std::integral T, typename U>
U pick(const T v, const U u)
//@ requires true;
//@ ensures result == u;
{
  return u;
}

// Verified even though nothing instantiates it.
template <std::integral T>
T uninstantiated(const T v)
//@ requires 0 <= v && v < 10;
//@ ensures result == v * 3;
{
  return (T)(v + v + v);
}

int main()
//@ requires true;
//@ ensures true;
{
  unsigned char c = clamp100<unsigned char>(200);
  //@ assert c == 100;
  long long ll = clamp100(5LL);
  //@ assert ll == 5;
  long d = dec(5L);
  //@ assert d == 4;
  uint16_t n = count_to<uint16_t>(3);
  //@ assert n == 3;
  bool digit = is_digit(7);
  //@ assert digit;
  short s = convert<long, short>(42);
  //@ assert s == 42;
  char32_t t = twice<char32_t>(21);
  //@ assert t == 42;
  int f = declared_first(3);
  //@ assert f == 4;
  long *p = 0;
  long *q = pick(1, p);
  //@ assert q == p;
  return 0;
}
