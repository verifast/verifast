int add(int x, int y)
//@ requires true;
//@ ensures true;
{
  return /*@ truncating @*/ (x + y); //~should_fail
}
