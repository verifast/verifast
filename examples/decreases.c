void m(int i)
  //@ requires 0<=i &*& i <= 10;
  //@ ensures true;
{
  while(i < 10) 
    //@ invariant 0 <= i &*& i <= 10;
    //@ decreases 10 - i;
  {
    i = i + 1;
  }
}