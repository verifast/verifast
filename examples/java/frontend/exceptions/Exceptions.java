class MyException extends Exception 
{
}

public class Exceptions
{  
  private static void test(boolean throw_or_not) throws MyException /*@ ensures throw_or_not == true; @*/ 
    //@ requires true;
    //@ ensures throw_or_not == false;
  {
    int i;
    
    if (throw_or_not)
      throw new MyException();
  }
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //@ int branch = 0;
    
    //Unchecked
    Object i = null;
    try
    {
      if (i == null)
        throw new NullPointerException();
      
      //@ branch = 1;
    }
    catch (NullPointerException e)
    {
      //@ branch = 2;
    }    
    //@ assert (branch == 2);
    
    //Checked
    //@ branch = 0;
    try
    {
      test(false);
      //@ branch = 1;
    }
    catch (MyException e)
    {
      //@ branch = 2;
    }
    //@ assert (branch == 1);
    
    //@ branch = 0;
    try
    {
      test(true);
      //@ branch = 1;
    }
    catch (MyException e)
    {
      //@ branch = 2;
    }
    //@ assert (branch == 2);
  }
}


