void array_test1(int* a)
  //@ requires a[0..3] |-> ?vs;
  //@ ensures a[0..3] |-> vs;
{
  int tmp0 = a[0];
  int tmp1 = a[1];
  int tmp2 = a[2];
}

void array_test2(int* a)
  //@ requires a[..?n] |-> ?vs &*& 1 < n;
  //@ ensures a[..n] |-> update(0, 10, vs);
{
  int a1_old = a[1];
  a[0] = 10;
  int tmp = a[0];
  assert(tmp == 10);
  int a1 = a[1];
  assert(a1_old == a1);
}

int to_verify(int* arr)
//@ requires arr[..10] |-> {0, 10, 20, 30, 40, 50, 60, 70, 80, 90};
//@ ensures arr[..10] |-> {0, 10, 20, 31, 40, 50, 60, 70, 80, 90} &*& result == 30;
{
  return arr[3]++;
}

//@ predicate p(int* a, int n;) = a[0..n] |-> ?vs &*& 0 < n;

void array_test_fail(int* a, int n)
  //@ requires a[0..5] |-> _;
  //@ ensures a[0..5] |-> _;
{
  a[-1] = 0; //~ should_fail
}

void array_test_fail2(int* a, int n)
  //@ requires a[0..5] |-> ?vs;
  //@ ensures a[0..5] |-> ?vs2;
{
  a[5] = 0; //~ should_fail
}

