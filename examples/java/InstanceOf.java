interface I {
}

class A implements I {
}

class B extends A {
}

class Program {
  void test(A[] a) 
    //@ requires true;
    //@ ensures true;
  {
    if(! (a instanceof B[])) {
    }
    
    if(a instanceof I[]) {
    }
  }
}