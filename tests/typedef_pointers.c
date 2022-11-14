typedef int I_t;

void f()
//@ requires true;
//@ ensures true;
{
  int const * p0 = 0;
  int * const p1 = 0;
  I_t const * cip0 = 0;
  I_t * const cip1 = 0;
}

void g()
//@ requires true;
//@ ensures true;
{
  int * a, b;
  I_t * c, d;
}
