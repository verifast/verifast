class C {
  static int id(int x)
    //@ requires true;
    //@ ensures result == x;
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  A() 
   //@ requires true;
   //@ ensures this.a |-> 1 &*& this.b |->  2;
  {
   
  }
  
  int getA() 
    //@ requires this.a |-> ?v;
    //@ ensures this.a |-> v &*& result == v;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
    //@ requires true;
    //@ ensures this.a |-> 1 &*& this.b |-> 2 &*& this.c |-> 1 &*& this.d |-> 11;
  {
    super();
  }
  
}
