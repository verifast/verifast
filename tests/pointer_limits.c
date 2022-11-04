void test_pointer_arithmetic()
//@ requires true;
//@ ensures true;
{
  char foo[2];
  char *pfoo = foo;
  char *bad_null = pfoo - (uintptr_t)pfoo; //~should_fail
}

void test_address_of_subscript()
//@ requires true;
//@ ensures true;
{
  char foo[2];
  //@ char__limits(foo);
  char *pfoo = foo;
  char *bad_ptr = &pfoo[UINTPTR_MAX]; //~should_fail
  //@ produce_limits(bad_ptr); //~allow_dead_code
  //@ assert false; //~allow_dead_code
}

struct foo { int x; int y; } __attribute__((packed));

void test_address_of_field()
//@ requires true;
//@ ensures true;
{
  struct foo *p = (struct foo *)UINTPTR_MAX;
  int *q = &p->y; //~should_fail
  //@ produce_limits(q); //~allow_dead_code
  //@ assert false; //~allow_dead_code
}