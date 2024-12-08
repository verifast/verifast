#include <assert.h>

void ptr_set(char **p, char *msg)
//@ requires *p |-> _;
//@ ensures *p |-> msg;
{
  *p = msg;
}

void char_set(char *a)
//@ requires character(a, _);
//@ ensures character(a, 'b');
{
  a[0] = 'b';
}

void test()
//@ requires true;
//@ ensures true;
{
  char *const p = 0;
  ptr_set((char **)&p, "Hello"); //~should_fail
}

int main(void)
//@ requires true;
//@ ensures true;
{
  const char *p = 0;
  const char z = 0;

  ptr_set((char **)&p, "Hello");
  char_set((char *)&z); //~should_fail
  assert(z == 'b'); //~allow_dead_code

  return 0; //~allow_dead_code
}
