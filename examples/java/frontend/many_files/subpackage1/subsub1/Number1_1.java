package subpackage1.subsub1;

public class Number1_1
{
  static public int getNumber()
    //@ requires true;
    //@ ensures result == 11;
  {
    return 11;
  }
}
