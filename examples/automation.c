
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

void test7(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [f]chars(c, 0, nil);
{
}

void test8(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [_]chars(c, 0, nil);
{
}

//@ predicate pos(int x;) = x == 0 ? true : pos(x - 1);

void test9()
  //@ requires true;
  //@ ensures pos(0);
{
}

void test9b()
  //@ requires true;
  //@ ensures pos(1);
{
}

void test10()
  //@ requires pos(7);
  //@ ensures pos(8); 
{
}

//@ predicate pos0(int x;) = x == 0 ? true : pos0(x - 1);

/*@
lemma_auto void pos_to_pos0()
  requires pos(?x);
  ensures pos0(x);
{
  open pos(x);
  if(x != 0)
    pos_to_pos0();
}
@*/


void test11()
  //@ requires pos(?x);
  //@ ensures pos0(x);
{
}

/*@
lemma_auto void pos0_to_pos(int x)
  requires [?f]pos0(x);
  ensures [f]pos(x);
{
  open [f]pos0(x);
  if(x != 0)
    pos0_to_pos(x - 1);
}
@*/

void test12()
  //@ requires [1/2]pos0(?x);
  //@ ensures [1/2]pos(x);
{
}

/* todo
//@ predicate foo(char* c, real f;) = [f]chars(c, 0, nil); 
//@ predicate bar(char* c, real f;) = [1/4]foo(c, f);
//@ predicate bar_(char* c, real f;) = [_]foo(c, f);

void test9(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [1/2]foo(c, f);
{
}

void test10(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [_]foo(c, f);
{
}

void test11(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [1/2]bar(c, f);
{
}

void test12(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [1/2]bar_(c, f);
{
}

void test13(char* c)
  //@ requires [_]exists<real>(?f);
  //@ ensures [_]bar(c, f);
{
}
*/