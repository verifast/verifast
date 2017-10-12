void test()
//@ requires exists<int>(?v) &*& v != 4;
//@ ensures exists<int>(v) &*& v == 4; //~ should_fail
{
  //@ v = 4;
}

void test2()
//@ requires true;
//@ ensures false; // <-- !
{
  //@ close exists(5);
  test();
}
