public class Super implements Inter
{
  public int increment(int i)
    //@ requires i < 100;
    //@ ensures result == i + 1;
  {
    return ++i;
  }
}
