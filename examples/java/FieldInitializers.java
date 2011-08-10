class A {
  int x = 5;
  
  A() 
   //@ requires true;
   //@ ensures this.x |-> 5;
  {
   
  }
}

class B extends A {

  int y = this.x;
  
  B() 
    //@ requires true;
    //@ ensures this.x |-> 5 &*& this.y |-> 5;
  {
    super();
  }
  
}
