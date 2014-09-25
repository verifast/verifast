public class A {
  //@ predicate valid() = emp; //this.x |-> x;
  
  public A()
  //@ requires true;
  //@ ensures valid();
  {
    //@ close valid();
  }

  public void m()
    // Does not seem to be exploitable without the "== ( ... ? ...)" construct.
    // Does not seem to be exploitable when using an even number instead of 21, or when deviding by something else than 2 (not tried all possibilities...)
    // Does not seem to work when replacing "<=" with "<". (of course, it can never be equal).
    //@ requires exists<int>(?y) &*& exists<int>(?z) &*& z == (y <= (21/2) ? 0 : 1); //mypred(?y, ?z);
    //@ ensures emp &*& false;
  {
    //@ assert false; // <--- How is this possible? (only z3 greenbars this).
  }
}


public class B {
   public B()
  //@ requires true;
  //@ ensures false;
  {
    A a = new A();
    //@ close exists(0);
    //@ close exists(0);
    // So we started with true as precondition, now call the method.
    a.m();
    // and now we also have false.
  }
}

