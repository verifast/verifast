// Increments a number of different types
// Looking to insure inc is not verified 21 times

#include <concepts>
#include <stdint.h>

// Because T is constrained by std::integral, inc is verified once, for every
// integer type other than bool
template <std::integral T>
T inc(const T v)
//@ requires v < 100;
//@ ensures result == v + 1;
{
  // The cast is needed for types narrower than int, where v + 1 is an int.
  return (T)(v + 1);
}

int main()
//@ requires true;
//@ ensures true;
{
  // Builtin integer types
  char c = inc<char>(1);
  //@ assert c == 2;
  signed char sc = inc<signed char>(1);
  //@ assert sc == 2;
  unsigned char uc = inc<unsigned char>(1);
  //@ assert uc == 2;
  short s = inc<short>(1);
  //@ assert s == 2;
  unsigned short us = inc<unsigned short>(1);
  //@ assert us == 2;
  int i = inc<int>(1);
  //@ assert i == 2;
  unsigned u = inc<unsigned>(1);
  //@ assert u == 2;
  long l = inc<long>(1);
  //@ assert l == 2;
  unsigned long ul = inc<unsigned long>(1);
  //@ assert ul == 2;
  long long ll = inc<long long>(1);
  //@ assert ll == 2;
  unsigned long long ull = inc<unsigned long long>(1);
  //@ assert ull == 2;

  // Fixed-width integer types from stdint.h
  int8_t i8 = inc<int8_t>(1);
  //@ assert i8 == 2;
  int16_t i16 = inc<int16_t>(1);
  //@ assert i16 == 2;
  int32_t i32 = inc<int32_t>(1);
  //@ assert i32 == 2;
  int64_t i64 = inc<int64_t>(1);
  //@ assert i64 == 2;
  uint8_t u8 = inc<uint8_t>(1);
  //@ assert u8 == 2;
  uint16_t u16 = inc<uint16_t>(1);
  //@ assert u16 == 2;
  uint32_t u32 = inc<uint32_t>(1);
  //@ assert u32 == 2;
  uint64_t u64 = inc<uint64_t>(1);
  //@ assert u64 == 2;

  // Arguments are checked against the precondition at each call.
  long big = inc<long>(99);
  //@ assert big == 100;

  return 0;
}
