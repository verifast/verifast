class A {
  int x1;    
  public A(int v) 
    //@ requires true;
    //@ ensures this.x1 |-> v;
  {
    super();
    x1 = v;
  }
}

class B extends A
{   int x2;
  
  public B(int v1, int v2) 
    //@ requires true;
    //@ ensures this.x1 |-> v1 &*& this.x2 |-> v2;
  {
    super(v1);
    this.x2 = v2;
  }
}

