class A {
  int x;

  public int m() 
    //@ requires valid(?v);
    //@ ensures valid(v) &*& result == v;
  {
    //@ open valid(v);
    int tmp = x; 
    //@ close valid(v);
    return tmp;
  }

  //@ predicate valid(int v) = this.x |-> v &*& 0 <= v;
}

class B extends A {
  //@ predicate valid(int v) = this.x |-> v &*& 0 <= v;

  public int m() 
    //@ requires valid(?v);
    //@ ensures valid(v) &*& result == v;
  {
    //@ A a = this;
    //@ open valid(v);
    //@ close a.valid(v);
    int tmp = super.m();
   //@ open a.valid(v);
   //@ close valid(v);
   return tmp;
  }
}