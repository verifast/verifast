// A function template is verified even if nothing instantiates it.

template <typename T>
T first(const T x, const T y)
//@ requires true;
//@ ensures result == x; //~ should_fail
{
  return y;
}
