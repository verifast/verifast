//////////////////
// Simple examples
//////////////////

#define FOO         foo
#define FOO_BAR     foo ## bar
#define FOO_BAR_BAZ foo##bar##baz
#include "headertest/subdir/bar.h"

int test_foo(int FOO)
//@ requires FOO > 0;
//@ ensures result > 0;
{
  return foo;
}

int test_foobar(int FOO_BAR)
//@ requires FOO_BAR > 0;
//@ ensures result > 0;
{
  return foobar;
}

int test_foobarbaz(int FOO_BAR_BAZ)
//@ requires FOO_BAR_BAZ > 0;
//@ ensures result > 0;
{
  return foobarbaz;
}




//////////////////
// Number examples
//////////////////

#define FIRST  first ## 1
#define SECOND sec ## 2 ## ond ## 2

int test_first(int FIRST)
//@ requires FIRST > 0;
//@ ensures result > 0;
{
  return first1;
}

int test_second(int SECOND)
//@ requires SECOND > 0;
//@ ensures result > 0;
{
  return sec2ond2;
}

#define TEN      TEN_1 ## 0
#define THOUSAND THOUSAND_1##0##0##0
#define SIX      SIX_6 ## 6 ## 6 ## 6
#define NINES    NINES_99 ## 99 ## 9

int test_ten(int TEN)
//@ requires TEN > 0;
//@ ensures result > 0;
{
  return TEN_10;
}

int test_thousand(int THOUSAND)
//@ requires THOUSAND > 0;
//@ ensures result > 0;
{
  return THOUSAND_1000;
}

int test_six(int SIX)
//@ requires SIX > 0;
//@ ensures result > 0;
{
  return SIX_6666;
}

int test_nines(int NINES)
//@ requires NINES > 0;
//@ ensures result > 0;
{
  return NINES_99999;
}




///////////////////////////
// Macro arguments examples
///////////////////////////

#define INDEXED(i) index_ ## i
#define DOUBLE_INDEXED(i, j) index_##i## __ ##j##_

int test_indexed(int INDEXED(5))
//@ requires INDEXED(5) > 0;
//@ ensures result > 0;
{
  return index_5;
}

int test_double_indexed(int DOUBLE_INDEXED(5, 6))
//@ requires DOUBLE_INDEXED(5, 6) > 0;
//@ ensures result > 0;
{
  return index_5__6_;
}




//////////////////
// Nested examples
//////////////////

#undef  FOO
#define FOO int fo ## o
int test_base(FOO)
//@ requires foo > 0;
//@ ensures result > 0;
{
  return foo;
}

#define NESTED1 FOO,int bar
int test_nested1(NESTED1)
//@ requires foo > 0 &*& bar > 0;
//@ ensures result > 0;
{
  return foo;
}


#define NESTED2    FOO ## bar ## baz
int test_nested2(int NESTED2)
//@ requires NESTED2 > 0;
//@ ensures result > 0;
{
  return FOObarbaz;
}

#define NESTED3(i) FOO ## i
int test_nested3(int NESTED3(bar))
//@ requires NESTED3(bar) > 0;
//@ ensures result > 0;
{
  return FOObar;
}

#define NESTED4(i) i ## foo
int test_nested4_1(int NESTED4(bar))
//@ requires NESTED4(bar) > 0;
//@ ensures result > 0;
{
  return barfoo;
}

#define TEST 3
int test_nested4_2(int NESTED4(TEST))
//@ requires NESTED4(TEST) > 0;
//@ ensures result > 0;
{
  return TESTfoo;
}

#define TEST2 3
#define NESTED5(a, b, c, d, e, f) a b ## c,d e ## f
int test_nested5(NESTED5(int, foo, TEST, char, bar, TEST2))
//@ requires fooTEST > 0 &*& barTEST2 > 0;
//@ ensures result > 0;
{
  int i = fooTEST;
  return barTEST2;
}

