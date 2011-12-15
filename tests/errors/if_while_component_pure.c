void ifTest()
  //@ requires true;
  //@ ensures true;
{
  int x = 0;

  if (2 == 3)
    //@ assert true; //~ should_fail
    x = 4;

  assert(x == 4);
}

void elseTest()
  //@ requires true;
  //@ ensures true;
{
  int x = 0;

  if (2 == 2);
  else
    //@ assert true; //~ should_fail
    x = 4;

  assert(x == 4);
}


void whileTest()
  //@ requires true;
  //@ ensures true;
{
  int x = 0;

  while (2 == 3)
    //@ invariant true;
    //@ decreases 0;
    //@ assert true; //~ should_fail
    x = 4;

  assert(x == 4);
}

void forTest()
  //@ requires true;
  //@ ensures true;
{
  int x = 0;

  for (x = 1; 2 == 3; x++)
    //@ invariant true;
    //@ decreases 0;
    //@ assert true; //~ should_fail
    x = 4;

  assert(x == 4);
}


void forSpecTest()
  //@ requires true;
  //@ ensures true;
{
  int x = 0;

  for (x = 1; 2 == 3; x++)
    //@ requires true;
    //@ ensures true;
    //@ decreases 0;
    //@ assert true; //~ should_fail
    x = 4;

  assert(x == 4);
}

