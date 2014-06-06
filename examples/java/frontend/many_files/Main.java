import subpackage1.*;
import subpackage2.*;
import subpackage3.*;

public class Main 
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    int add1 = Add1.add();
    int add2 = Add2.add();
    int add3 = Add3.add();
    int add  = add1 + add2 + add3;
    //@ assert add == 11 + 21 + 22 + 31 + 32 + 33;
    
    int mul1 = Multiply1.multiply();
    int mul2 = Multiply2.multiply();
    int mul3 = Multiply3.multiply();
    int mul  = mul1 * mul2 * mul3;
    //@ assert mul == 11 * 21 * 22 * 31 * 32 * 33;
  }
}
