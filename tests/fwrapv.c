int add(int x, int y)
//@ requires true;
//@ ensures result == truncating (x + y);
{
  return /*@ truncating @*/ (x + y);
}
