public abstract class A {
  void m()
    //@ requires true;
    //@ ensures true;
  {
  }
}

class B extends A {
  public void m()
    //@ requires true;
    //@ ensures true;
  {
  }
}