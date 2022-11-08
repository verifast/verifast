class A 
{
    int i;
  
    //@ predicate valid() = false;
      
    public int getI()
    //@ requires valid();
    //@ ensures valid();
    {
    	//@ open valid();
        return i/0; //~allow_dead_code
    }
}


class B extends A //~should_fail
{
    int j;
    
    //@ predicate valid() = this.i |-> ?m_i &*& this.j |-> ?m_j;
}

class Program {
    public void test(B b) 
      //@ requires b != null &*& b.valid();
      //@ ensures true;
    {
    	b.getI();
    }
}