class Division {
  int division_test(int nom, int denom) 
    //@ requires denom != 0;
    //@ ensures result == nom / denom;
  {
    int tmp = nom / denom;
    return tmp;
  }
  
  int division_test2(int nom, int denom) 
    //@ requires denom != 0;
    //@ ensures result == nom / denom;
  {
    int tmp = nom / denom;
    int rest = nom % denom;
    //@ assert denom*tmp + rest == nom;
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