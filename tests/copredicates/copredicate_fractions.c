/*@ copredicate mycopredicate(;) = mycopredicate(); 
@*/

void test()
//@ requires true &*& mycopredicate();
//@ ensures false;
{

  //@ open [1/2]mycopredicate();
  //@ open [1/2]mycopredicate();
  
  test();
  

}
