int foo()
//@ requires true;
//@ ensures true;
{
  int x;
  int *p = &x;
  return *p; //~should_fail
}
