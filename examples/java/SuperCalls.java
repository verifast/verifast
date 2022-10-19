class A {
  int x;

  public int m(int y) 
    //@ requires valid(?v) &*& 0 <= y;
    //@ ensures valid(y) &*& result == y;
  {
    //@ open valid(v);
    x = y;
    //@ close valid(y);
    return y;
  }

  //@ predicate valid(int v) = this.x |-> v &*& 0 <= v;
}

class B extends A {
  //@ predicate valid(int v) = this.x |-> v &*& 0 <= v;

  public int m(int y) 
    //@ requires valid(?v) &*& 0 <= y;
    //@ ensures valid(y) &*& result == y;
  {
    //@ open valid(v);
    //@ close valid(A.class)(v);
    int tmp = super.m(y);
   //@ open valid(A.class)(y);
   //@ close valid(y);
   return tmp;
  }
}