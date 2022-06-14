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
  
  //@ assert 0x1.8 == 1.5;
  //@ assert 0x1.8p-1 == 0.75;
  //@ assert 0xA.FF + 0x0.01 == 11;
  //@ assert 0x1p16 == 65536;
  //@ assert 0xff_0000_0000p-32 == 255;

  return 0;
}
