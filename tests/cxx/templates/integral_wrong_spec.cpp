// A function template constrained by std::integral is verified once, so its
// proof must hold for every integer type other than bool: the smallest and
// largest ones, signed and unsigned ones.

#include <concepts>

// Wrong for signed char: inc(150) does not fit.
template <std::integral T>
T inc(const T v)
//@ requires v < 200;
//@ ensures result == v + 1;
{
  return (T)(v + 1); //~ should_fail
}

// Wrong for unsigned types: dec(0) does not fit.
template <std::integral T>
T dec(const T v)
//@ requires v < 100;
//@ ensures result == v - 1;
{
  return (T)(v - 1); //~ should_fail
}

// Wrong for long: v * v can overflow.
template <std::integral T>
T square(const T v)
//@ requires true;
//@ ensures true;
{
  return (T)(v * v); //~ should_fail
}

// Wrong for unsigned types.
template <std::integral T>
void negative_one(const T v)
//@ requires true;
//@ ensures true;
{
  //@ assert v >= -1; //~ should_fail
}

// Wrong for signed char.
template <std::integral T>
T two_hundred(const T v)
//@ requires true;
//@ ensures true;
{
  return (T)200; //~ should_fail
}

// The facts about the limits of T are consistent.
template <std::integral T>
void consistent(const T v)
//@ requires true;
//@ ensures true;
{
  //@ assert false; //~ should_fail
}
