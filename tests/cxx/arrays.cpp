int firstElement(int array[])
//@ requires ints(array, ?len, ?vals) &*& len > 0;
//@ ensures ints(array, len, vals);
{
  return array[0];
}

int main()
//@ requires true;
//@ ensures true;
{
  int data[3] = {3, 4, 5};
  
  //@ assert(data[1] == 4);

  for(int i = 0; i < 3; ++i)
  //@ invariant 0 <= i &*& i <= 3 &*& ints_(data, 3, _);
  //@ decreases 3 - i;
  {
    data[i] = i;
  }
}
