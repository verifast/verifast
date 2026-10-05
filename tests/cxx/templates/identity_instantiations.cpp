// All these calls use the single generic proof of `identity`: it is verified
// once, with T as a type parameter, and not once per scalar type argument.

enum Color { Red, Green };

template <typename T>
T identity(const T x)
//@ requires true;
//@ ensures result == x;
{
  return x;
}

int main()
//@ requires true;
//@ ensures true;
{
  int i = identity(3);
  //@ assert i == 3;
  bool b = identity(true);
  //@ assert b;
  long l = identity(5L);
  //@ assert l == 5;
  unsigned u = identity(4u);
  //@ assert u == 4;
  char c = identity('x');
  //@ assert c == 'x';
  short s = identity<short>(7);
  //@ assert s == 7;
  Color color = identity(Green);
  //@ assert color == Green;
  int *p = identity(&i);
  //@ assert p == &i;
  return 0;
}
