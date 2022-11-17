int test(int i)
//@ requires 0 <= i && i < 100;
//@ ensures true;
{
  return i++ + i; //~should_fail
}
