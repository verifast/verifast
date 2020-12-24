class Program {

  public static void test(int[] xs)
    //@ requires array_slice(xs, 0, 10, _);
    //@ ensures array_slice(xs, 3, 2, _); //~should_fail
  {
  }

}
