//@ predicate opaque();

int foo()
//@ requires opaque();
//@ ensures opaque();
{
  return 0;
}

void bar()
//@ requires opaque();
//@ ensures opaque();
{
  (void)foo();
}
