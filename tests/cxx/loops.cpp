void f()
//@ requires true;
//@ ensures true;
{
  int i;
  const int n = 2;

  for(i = 0; i < n; ++i)
  //@ invariant 0 <= i &*& i <= n;
  //@ decreases n - i;
  {
    continue;
    //@ assert false;
  }
  //@ assert i == 2;
}

void g()
//@ requires true;
//@ ensures true;
{
  int i;
  const int n = 2;

  for(i = 0; i < n; ++i)
  //@ requires 0 <= i &*& i <= n;
  //@ ensures i == n;
  //@ decreases n - i;
  {
    continue;
    //@ assert false;
  }
  //@ assert i == 2;
}