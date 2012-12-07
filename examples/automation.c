
/*@
predicate myinteger(int* x; int v);

predicate_ctor eq_core(int* y)(; int w) = integer(y, w);

predicate_ctor is_zero()(; int x) = x == 0;

predicate_ctor eq(int* x)(;int v) = eq_core(x)(v);

predicate p(int* x; int v) =
  eq(x)(v) &*& character((void*)x + 1, 0);
  
predicate q(int* x; int v) =
  x == 0 ? v == 0 : p(x, v);
@*/

void test1(int* i)
 //@ requires q(i, ?v) &*& i != 0;
 //@ ensures eq(i)(v) &*& character((void*)i + 1, 0);
{
}

void test2(int* i, int* j)
 //@ requires eq(i)(0) &*& character((void*)i + 1, 0) &*& i != 0;
 //@ ensures q(i, 0);
{
}

void test3(int* i)
  //@ requires integer(i, 5);
  //@ ensures eq(i)(5);
{
  ////@ close eq(i)(5);
}

void test4(int* i)
  //@ requires q(i, 5) &*& i != 0;
  //@ ensures integer(i, 5) &*& character((void*)i + 1, 0);
{
}

void test5()
  //@ requires true;
  //@ ensures is_zero()(0);
{
  //@ close is_zero()(0); // todo, include predicate_ctors in empty_preds
}

void helper(int* x);
  //@ requires exists<predicate(;int)>(?I) &*& I(5);
  //@ ensures false;
  
void test6(int* i)
  //@ requires integer(i, 5);
  //@ ensures true;
{
  //@ close exists(eq(i));
  helper(i);
}