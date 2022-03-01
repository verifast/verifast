#include "stdlib.h"
/*@
predicate_ctor bor_int(real f)(int *px)= [f]integer(px,?v); //Chunk
predicate own_int(int *px;)=
malloc_block_ints(px,1) &*& integer(px,?v); //Actual size and del capability

/*inductive bor = |BorExc |BorShr;

predicate bor_int(bor b, int *px;) = switch(b) {
case BorExc: return exc_int(px);
case BorShr: return shr_int(px, 1.0);
};*/

predicate alpha_shr_int(list<int *> shr_int_rs)= foreach(shr_int_rs, bor_int(?f));
predicate alpha_exc_int(list<int *> exc_int_rs)= foreach(exc_int_rs, bor_int(1.0));
@*/

void test(int* x)
//@requires [1/2]exc_int(x);
//@ensures [1/2]exc_int(x);
{
	int y = *x;
}

int* new_int()
//@ requires true;
//@ ensures own_int(result);
{
	int *r = malloc(sizeof(int));
	if(r==0) abort();
	return r;	
}

/*
fn passive<'a|>(x:imm'a i32)->imm'a i32 {
let *y = copy *x;
drop y;
return x;
}
*/

int* passive(int* x)
/*@
requires alpha_shr_int({x});
@*/
/*@
ensures alpha_shr_int({x});
@*/
{
//int y = *x;
return x;
}