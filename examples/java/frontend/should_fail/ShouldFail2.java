public class ShouldFail2
{
  public static void test()
    //@ requires true;
    //@ ensures true;
  {
    int i = 0;
    //@ assert i == 0;
    i++;
    /*@
      {
        assert i == 2; //~
      }
    @*/
  }
}