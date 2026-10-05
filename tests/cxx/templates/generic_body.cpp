// Constructs that function templates can use in their body, which is verified
// once with abstract type parameters.

template <typename T>
T copy_through_locals(T x)
//@ requires true;
//@ ensures result == x;
{
  T y = x;
  T z;
  z = y;
  //@ T g = z;
  //@ assert g == x;
  return z;
}

template <typename T, typename U>
U second(T x, U y)
//@ requires true;
//@ ensures result == y;
{
  // Calls that do not depend on a type parameter are resolved in the template.
  int i = copy_through_locals(1);
  //@ assert i == 1;
  return y;
}

template <typename T>
T declared_first(T x);
//@ requires true;
//@ ensures result == x;

template <typename T>
T declared_first(T x)
//@ requires true;
//@ ensures result == x;
{
  return x;
}

template <typename T>
void assign(T &r, const T v)
//@ requires r |-> _;
//@ ensures r |-> v;
{
  r = v;
}

template <typename T>
T &same_ref(T &r)
//@ requires true;
//@ ensures &result == &r;
{
  return r;
}

int main()
//@ requires true;
//@ ensures true;
{
  long l = copy_through_locals(5L);
  //@ assert l == 5;
  char c = second(1, 'x');
  //@ assert c == 'x';
  unsigned u = declared_first(4u);
  //@ assert u == 4;
  int i = 0;
  assign(i, 9);
  //@ assert i == 9;
  int &r = same_ref(i);
  return 0;
}
