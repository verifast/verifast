long long shift_left_negative_amount()
//@ requires true;
//@ ensures true;
{
  return 1LL << -1; //~ should_fail
}

long long shift_left_excessive_amount()
//@ requires true;
//@ ensures true;
{
  return 1LL << 63; //~ should_fail
}

long long shift_left_negative_value()
//@ requires true;
//@ ensures true;
{
  return -1 << 3; //~ should_fail
}

long long shift_right_negative_amount()
//@ requires true;
//@ ensures true;
{
  return 1024LL >> -1; //~ should_fail
}

long long shift_right_excessive_amount()
//@ requires true;
//@ ensures true;
{
  return 1024LL >> 63; //~ should_fail
}

long long shift_right_negative_value()
//@ requires true;
//@ ensures true;
{
  return -1024LL >> 3; //~ should_fail
}
