package subpackage1;

import  subpackage1.subsub1.Number1_1;

public class Multiply1
{
  static public int multiply()
    //@ requires true;
    //@ ensures result == 11;
  {
    return 1 * Number1_1.getNumber();
  }
}
