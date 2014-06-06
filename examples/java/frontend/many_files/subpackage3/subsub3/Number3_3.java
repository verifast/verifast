package subpackage3.subsub3;

public class Number3_3
{
  public static int getNumber()
    //@ requires true;
    //@ ensures result == 33;
  {
    return 33;
  }
}
