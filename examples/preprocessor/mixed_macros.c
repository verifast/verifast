#define FOUR 4
#define FIVE 5

/*@
#define MACRO FOUR
@*/

void test0()
//@ requires true;
//@ ensures true;
{
  int MACRO = 0;
  int number2 = 4;

  //@ assert number2 == MACRO;
}

/*@
#undef MACRO
@*/

#define MACRO FIVE

void test1()
//@ requires true;
//@ ensures true;
{
  int num = MACRO;

  //@ assert num == MACRO;
}

/*@
#define MACRO FIVE + 1
@*/

void test2()
//@ requires true;
//@ ensures true;
{
  int num = MACRO;

  //@ assert num == MACRO - 1;
}

/*@
#undef MACRO
@*/

void test3()
//@ requires true;
//@ ensures true;
{
  int num = MACRO;

  //@ assert num == MACRO;
}

#undef MACRO

void test4()
//@ requires true;
//@ ensures true;
{
  /*~*/int num = MACRO;
}
