#define FOO         foo
#define FOO_BAR     foo ## bar
#define FOO_BAR_BAZ foo##bar##baz

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

#define TEN      1 ## 0
#define THOUSAND 1##00##0
#define NINES    9 ## 009 ## 00 ## 9

int test_ten()
//@ requires true;
//@ ensures result == 10;
{
  return TEN;
}

int test_thousand()
//@ requires true;
//@ ensures result == 1000;
{
  return THOUSAND;
}

int test_nines()
//@ requires true;
//@ ensures result == 9009009;
{
  return NINES;
}

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





