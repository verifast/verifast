public class Sub extends Super //~
{
  public int increment(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    int j = i;
    j++;
    return j;
  }

  public int dummy(int i)
    //@ requires true;
    //@ ensures result == i;
  {
    return i;
  }
}
