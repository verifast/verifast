class DivisionOverflow {
  int division_test_fail_overflow(int nom, int denom)
    //@ requires denom != 0;
    //@ ensures result == nom / denom;
  {
    int tmp = nom / denom; //~ should_fail
    return tmp; //~allow_dead_code
  }
}