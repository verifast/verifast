import subpackage.Multiply;

public class Main 
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true; 
  {
    Multiply mul = new Multiply();
    int i = mul.multiply();
    //@ assert i == 30;
  }
}
