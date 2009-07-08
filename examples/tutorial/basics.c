int main()
  //@ requires true;
  //@ ensures true;
{
  int i = 10;
  i = i + 1;
  
  assert(i == 11);
  
  return 0;
}