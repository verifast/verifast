public interface Inter
{
  public int increment(int i);
    //@ requires i < 100;
    //@ ensures result == i + 1;
}
