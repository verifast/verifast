int main()
//@ requires true;
//@ ensures true;
{
  int x;
  return x; //~ should_fail
}

int main2(bool b)
//@ requires true;
//@ ensures true;
{
  int x;
  while (true)
  //@ invariant true;
  {
    if (b)
      return x; //~ should_fail
    else
      x = 3; //~allow_dead_code
  }
}

int main3(bool b)
//@ requires true;
//@ ensures true;
{
  int x;
loop:
  //@ invariant true;
  if (b)
    return x; //~should_fail
  else
    x = 3; //~allow_dead_code
  goto loop; //~allow_dead_code
}

int main4(bool b)
//@ requires true;
//@ ensures true;
{
  int x;
  int y;
  while (true)
  //@ requires true;
  //@ ensures true;
  {
    if (b)
      y = x / 2; //~should_fail
    else
      x = 3; //~allow_dead_code
  }
}