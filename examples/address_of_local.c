// doesn't verify yet

void swap(int* a, int* b)
  //@ requires integer(a, ?av) &*& integer(b, ?bv);
  //@ ensures integer(a, bv) &*& integer(b, av);
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

void test() 
  //@ requires true;
  //@ ensures true;
{
    int x = 5; 
    int y = 10;
    swap(&x, &y);
    assert(x == 10);
}