#define NULL 0

// this macro has two parameters:
#define SUM(x,y) (x+y)

// this macro has no parameters at all. Even though this line contains brackets.
#define FIVE (2+3)

#define FIVE_NO_BRACKETS 2+3

// A more realistic example (now with tabs as separator)
#define CONSTANT1	0x10
#define CONSTANT2	0x20
#define SOME_MASK	(CONSTANT1 | CONSTANT2)

void test()
//@ requires true;
//@ ensures true;
{
  int zero = NULL;
  int x = SUM(1,SUM(zero, 3));
  //@ assert x == 4;
  
  x = FIVE*2;
  //@ assert x == 10;
  
  x = FIVE_NO_BRACKETS*2;
  //@ assert x == 8;
  
  x = SOME_MASK;
}


// Should also work for ghostcode:
/*@
#define NULL 0
#define SUM(x,y) (x+y)
#define FIVE (2+3)
#define FIVE_NO_BRACKETS 2+3
#define CONSTANT1 0x10
#define CONSTANT2 0x20
#define SOME_MASK (CONSTANT1 | CONSTANT2)

lemma void test_ghost()
  requires true;
  ensures true;
{
  int zero = NULL;
  int x = SUM(1,SUM(zero, 3));
  assert x == 4;
  
  x = FIVE*2;
  assert x == 10;
  
  x = FIVE_NO_BRACKETS*2;
  assert x == 8;
  
  x = SOME_MASK;
}
@*/
