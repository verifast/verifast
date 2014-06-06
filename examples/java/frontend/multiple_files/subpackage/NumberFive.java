package subpackage;

public class NumberFive
{
  int getFive()
    //@ requires true;
    //@ ensures result == 5;
  {
    return 5;
  }
}
