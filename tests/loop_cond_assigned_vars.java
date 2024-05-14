class Test {

  static void test_inv_loop()
  //@ requires true;
  //@ ensures false; //~should_fail
  {
    int i = 0;
    int j = 0;
    while (i++ != 100)
    //@ invariant i == j &*& i <= 100;
    {
      j++;
    }
  }

  static void test_spec_loop()
  //@ requires true;
  //@ ensures false; //~should_fail
  {
    int i = 0;
    int j = 0;
    while (i++ != 100)
    //@ requires i == j &*& i <= 100;
    //@ ensures true;
    {
      j++;
    }
  }
  
}