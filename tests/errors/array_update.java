class Test {

  static void test(int[] xs)
    //@ requires [_]xs[..1] |-> _;
    //@ ensures true;
  {
    xs[0] = 42; //~should_fail
  }

}
