class A 
{
    int i;
  
    //@ predicate valid() = false;
      
    public int getI()
    //@ requires valid();
    //@ ensures valid();
    {
    	//@ open valid();
        return i;
    }
}


class B extends A //~
{
    int j;
    
    //@ predicate valid() = this.j |-> ?m_j;
}

class Program {
    public void test(B b) 
      //@ requires b != null &*& b.valid();
      //@ ensures true;
    {
    	b.getI();
    }
}