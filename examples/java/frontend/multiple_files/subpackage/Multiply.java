package subpackage;

public class Multiply
{
  public int multiply()
    //@ requires true;
    //@ ensures result == 30;
  {
    NumberFive five = new NumberFive();
    NumberSix six = new NumberSix();
    return five.getFive() * six.getSix();
  }
}
