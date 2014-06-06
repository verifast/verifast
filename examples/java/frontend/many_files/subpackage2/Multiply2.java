package subpackage2;

import  subpackage2.subsub1.Number2_1;
import  subpackage2.subsub2.Number2_2;

public class Multiply2
{
  static public int multiply()
    //@ requires true;
    //@ ensures result == 21 * 22;
  {
    return 1 * Number2_1.getNumber() * Number2_2.getNumber();
  }
}
