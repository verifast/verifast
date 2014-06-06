package subpackage3;

import  subpackage3.subsub1.Number3_1;
import  subpackage3.subsub2.Number3_2;
import  subpackage3.subsub3.Number3_3;

public class Add3
{
  static public int add()
    //@ requires true;
    //@ ensures result == 31 + 32 + 33;
  {
    return 0 + Number3_1.getNumber() + Number3_2.getNumber() + Number3_3.getNumber();
  }
}