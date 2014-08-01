abstract class A {
  //@ predicate valid() = true;

  public abstract void m();
    //@ requires valid();
    //@ ensures valid();
}

class B extends A {
  int x;
  
  //@ predicate valid() = x |-> ?v;

  public void m()
    //@ requires valid();
    //@ ensures valid();
  {
    //@ open valid();
    x = 0;
    //@ close valid();
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    //@ requires a != null &*& a.valid();
    //@ ensures true;
  {
    a.m();
  }
}