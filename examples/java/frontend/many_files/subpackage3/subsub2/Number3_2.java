package subpackage3.subsub2;

public class Number3_2
{
  public static int getNumber()
    //@ requires true;
    //@ ensures result == 32;
  {
    return 32;
  }
}
