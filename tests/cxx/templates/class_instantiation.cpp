// A specialization whose type arguments are not all scalar types does not use
// the generic proof of its template. It is verified separately, so that the
// contracts of the copy constructors and destructors it calls are checked.

struct Point
{
  int m_x;

  Point(int x) : m_x(x)
  //@ requires true;
  //@ ensures this->m_x |-> x;
  {}

  ~Point()
  //@ requires this->m_x |-> _;
  //@ ensures true;
  {}
};

template <typename T>
T *ptr_identity(T *p)
//@ requires true;
//@ ensures result == p;
{
  return p;
}

int main()
//@ requires true;
//@ ensures true;
{
  Point point(1);
  Point *q = ptr_identity(&point); // verified separately, as ptr_identity(Point *)
  //@ assert q == &point;
  int i = 0;
  int *r = ptr_identity(&i); // uses the generic proof
  //@ assert r == &i;
  return 0;
}
