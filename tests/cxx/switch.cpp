enum numbers { zero, one, two };

void m(int i) 
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  switch(i) {
    case one:
      j = 2;
      break;
    case two:
      j = 2;
      break;
    default:
      j = 3;
      break;
  }
  if(i == 1 || i == 2) {
    //@ assert(j == 2);
  } else {
    //@ assert(j == 3);
  } 
}

void n(int i)
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  int t = 0;
  switch(i) {
    case 1:
      j = 1;
    case 2:
      j = 2;
      t = 2;
      break;
  }
  //@ assert(j == 2 && t == 2 || j == 0 && t == 0);
}

void unreachable(int i)
  //@ requires true;
  //@ ensures true;
{
  int j = 0;
  switch(i) j = 1; //~allow_dead_code
  //@ assert j == 0;
}

void single_default_label(int i)
  //@ requires true;
  //@ ensures true;
{
  int j;
  switch(i) default: j = 1;
  //@ assert j == 1;
}

void single_labels()
  //@ requires true;
  //@ ensures true;
{
  int i(0);
  switch (i) case 1: i += 1; //~allow_dead_code
  //@ assert i == 0;
  switch (i) case 0: i += 1;
  //@ assert i == 1;
}

void nested() 
  //@ requires true;
  //@ ensures true;
{
  int i(0);
  int j(2);
  int r;
  switch (i)
  {
  case 0:
    switch (j)
    {
    case 1:
      r = 1; //~allow_dead_code
      break; //~allow_dead_code
    default:
      break; //~allow_dead_code
    case 2:
      //@ assert i == 0;
      r = 2;
    }
    break;
  case 1:
    r = -1; //~allow_dead_code
  default:
    break; //~allow_dead_code
  }
  //@ assert r == 2;
}

void fallthrough()
  //@ requires true;
  //@ ensures true;
{
  int i(1);
  int j(0);
  switch (i)
  {
  case 1:
    //@ assert j == 0;
    j = 1;
  case 2:
    j += 1;
    //@ assert j == 2;
  case 3:
    j += 1;
    //@ assert j == 3;
  case 4:
    //@ assert j == 3;
    {
      j += 1;
      //@ assert j == 4;
      j = 0;
    }
  }
  //@ assert j == 0;
}