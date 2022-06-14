#include <math.h>

int main()
//@ requires true;
//@ ensures true;
{
  float f = 42;
  //@ real_of_int_of_decimal("42");
  //@ assert fp_of_float(f) == fp_real(42);
  double d = -127;
  //@ real_of_int_of_decimal("-127");
  //@ assert fp_of_double(d) == fp_real(-127r);
  return 0;
}
