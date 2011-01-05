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

/*@
lemma void le_mult_compat(int x, int y1, int y2)
    requires 0 <= x &*& y1 <= y2;
    ensures x * y1 <= x * y2;

{
  int i = x;
  while(0 < i) 
    invariant 0 <= i &*& i <= x &*& x * y1 - i * y1 <= x * y2 - i * y2;
    decreases i;
  {
    i = i - 1;
  }
}
@*/