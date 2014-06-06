package subpackage2.subsub1;

public class Number2_1
{
  public static int getNumber()
    //@ requires true;
    //@ ensures result == 21;
  {
    return 21;
  }
}
