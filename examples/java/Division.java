class Division {
  int division_test(int nom, int denom) 
    //@ requires denom != 0;
    //@ ensures result == nom / denom;
  {
    int tmp = nom / denom;
    return tmp;
  }
  
  int division_test_fail(int nom, int denom) 
    //@ requires true;
    //@ ensures result == nom / denom;
  {
    int tmp = nom / denom; //~ should_fail
    return tmp;
  }
}