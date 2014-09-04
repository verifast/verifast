abstract class A 
{
  //@ predicate pred() = true;

  public A()
    //@ requires true;
    //@ ensures pred();
  {
    //@ close pred();
  }

  public void m()
    //@ requires pred();
    //@ ensures pred();
  {
  }
}

class B extends A //~
{
  public B()
    

  {
    super();
  }
}

class C 
{
  public void m()


  {
    B b = new B();
  }
}
