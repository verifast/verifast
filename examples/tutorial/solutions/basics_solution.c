int inc(int x)
  //@ requires true;
  //@ ensures result == x + 1;
{
  x = x + 1;
  return x; // result = j;
}

int abs(int x)
  //@ requires true;
  //@ ensures 0 <= x ? result == x: result == 0 - x;
{
  if(0<=x) {
    return x;
  } else {
    return 0 - x;
  }
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int i = 0 - 10;
  i = inc(i);
  
  i = abs(i);
  
  //@ assert i == 9;
  
  return 0;
}