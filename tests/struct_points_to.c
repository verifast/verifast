struct foo;

void swap_foo(struct foo *f1, struct foo *f2)
//@ requires *f1 |-> ?v1 &*& *f2 |-> ?v2;
//@ ensures *f1 |-> v2 &*& *f2 |-> v1;
{
  struct foo tmp = *f1;
  *f1 = *f2;
  *f2 = tmp;
}
