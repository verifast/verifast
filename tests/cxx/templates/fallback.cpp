// A function template whose C++ body could be verified generically, but whose
// generic function does not type-check, is verified per specialization, as if
// it could not be verified generically. Here, its annotations only type-check
// for particular type arguments.

template <typename T>
T identity(const T x)
//@ requires true;
//@ ensures result == x;
{
  return x;
}

// The contract only type-checks for arithmetic type arguments.
template <typename T>
T positive(const T x)
//@ requires x > 0;
//@ ensures result == x;
{
  return x;
}

// v has type T, so `v == 0` only type-checks for arithmetic type arguments.
template <typename T>
void keep_zero(T *p)
//@ requires *p |-> ?v &*& v == 0;
//@ ensures *p |-> v;
{}

// The ghost code in the body only type-checks for arithmetic type arguments.
template <typename T>
T keep_sign(const T x)
//@ requires true;
//@ ensures result == x;
{
  //@ assert x > 0 || x <= 0;
  return x;
}

template <typename T>
T declared_first(const T x);
//@ requires x < 10;
//@ ensures result == x;

template <typename T>
T declared_first(const T x)
//@ requires x < 10;
//@ ensures result == x;
{
  return x;
}

// Nothing instantiates this template, so it is not verified.
template <typename T>
T uninstantiated(const T x)
//@ requires x > 0;
//@ ensures result == x;
{
  return x;
}

int main()
//@ requires true;
//@ ensures true;
{
  int a = positive(3);
  //@ assert a == 3;
  long b = positive(4L);
  //@ assert b == 4;
  int *p = new int;
  *p = 0;
  keep_zero(p);
  delete p;
  int c = keep_sign(5);
  //@ assert c == 5;
  int d = declared_first(6);
  //@ assert d == 6;
  // identity is still verified generically.
  int e = identity(7);
  //@ assert e == 7;
  return 0;
}
