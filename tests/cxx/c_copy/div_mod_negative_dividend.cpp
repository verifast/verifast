void test()
  //@ requires true;
  //@ ensures true;
{
  //@ assert 5 / 3 == 1;
  //@ assert 5 % 3 == 2;
  //@ assert 5 / -3 == -1;
  //@ assert 5 % -3 == 2;
  //@ assert -5 / 3 == -1;
  //@ assert -5 % 3 == -2;
  //@ assert -5 / -3 == 1;
  //@ assert -5 % -3 == -2;
  //@ div_rem(-5, -3);
  //@ assert false; //~ should_fail
}
