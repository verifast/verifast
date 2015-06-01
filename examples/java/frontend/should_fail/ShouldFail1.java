public class ShouldFail1
{
  class Inner
  {
    String test() {return "inner";}
  }
  
  public static void test()
    //@ requires true;
    //@ ensures true;
  {
    Inner o;
    String foo = o.test(); //~
  }
}