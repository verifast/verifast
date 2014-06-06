package subpackage1;

import  subpackage1.subsub1.Number1_1;

public class Add1
{
  static public int add()
    //@ requires true;
    //@ ensures result == 11;
  {
    return 0 + Number1_1.getNumber();
  }
}