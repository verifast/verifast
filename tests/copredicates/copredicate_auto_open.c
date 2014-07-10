/*@ copredicate mycopredicate(int x;) = mycopredicate(x + 1); 
@*/

void test(int x)
//@ requires mycopredicate(x);
//@ ensures false;
{
  test(x+1);
}
