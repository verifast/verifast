class A 
{
    int i;
  
    //@ predicate valid() = this.i |-> ?m_i;
      
    public int getI()
    //@ requires valid();
    //@ ensures valid();
    {
        return i;
    }
}


class B extends A
{
    int j;
    
    //@ predicate valid() = this.valid(A.class)() &*& this.j |-> ?m_j;

    public int getI()
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        return super.getI();
        //@ close valid();
    }
}

class Program {
    public void test(B b) 
      //@ requires b != null &*& b.valid();
      //@ ensures true;
    {
    	b.getI();
    }
}