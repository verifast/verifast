class A {
  int a = 1, b = 2;
  
  A() 
   //@ requires true;
   //@ ensures this.a |-> 1 &*& this.b |->  2;
  {
   
  }
}

class B extends A {

  int c = this.a, d = this.c + 10;
  
  B() 
    //@ requires true;
    //@ ensures this.a |-> 1 &*& this.b |-> 2 &*& this.c |-> 1 &*& this.d |-> 11;
  {
    super();
  }
  
}
