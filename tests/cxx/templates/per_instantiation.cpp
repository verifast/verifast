// These templates use their type parameter in ways whose meaning depends on the
// type argument, so they cannot be verified once for an abstract T. Each of
// their specializations is verified separately instead.

// What `==` does depends on T: for instance, `x == x` is false for a
// floating-point NaN.
template <typename T>
bool same(const T x, const T y)
//@ requires true;
//@ ensures result == (x == y);
{
  return x == y;
}

// The conversion from T to int depends on T.
template <typename T>
int to_int(const T x)
//@ requires true;
//@ ensures result == x;
{
  return x;
}

// The conversion from T to bool depends on T.
template <typename T>
bool is_nonzero(const T x)
//@ requires true;
//@ ensures result == (x != 0);
{
  if (x) {
    return true;
  }
  return false;
}

int main()
//@ requires true;
//@ ensures true;
{
  bool b = same(1, 1);
  //@ assert b;
  bool c = same(true, false);
  //@ assert !c;
  short s = 5;
  int i = to_int(s);
  //@ assert i == 5;
  bool n = is_nonzero(i);
  //@ assert n;
  return 0;
}
