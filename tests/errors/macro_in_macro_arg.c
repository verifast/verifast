// Repro produced by let-def (Frederic Bour)
// https://github.com/verifast/verifast/issues/123

#define ID(x) x
#define ONE 1

int test(void)
//@requires true;
//@ensures true;
{
  int x = ID(ONE * f()); //~ should_fail
  return x;
}
