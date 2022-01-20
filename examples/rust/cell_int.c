#include "stdlib.h"

/*@
predicate u_integer_exc(unsigned int* i; unsigned int v) = u_integer(i, v);
predicate u_integer_own(unsigned int *i; unsigned int v) = malloc_block_uints(i, 1) &*& u_integer_exc(i, v);
predicate u_integer_shr(unsigned int *i, unsigned int v) = [?p]u_integer(i, v) &*& p<=1.0;
@*/
// pub struct stde::cell_nat::CellNat<>{nat}
struct CellNat {
unsigned int value;
};
/*@
predicate CellNat_exc(struct CellNat* c; unsigned int v) = c->value |-> v;
predicate CellNat_own(struct CellNat* c; unsigned int v) =
malloc_block_CellNat(c) &*& CellNat_exc(c, v);
predicate CellNat_shr(struct CellNat* c; unsigned int v) = c->value |-> v;
@*/
/***
 * pub safe fn stde::cell_nat::new<|>(v: own nat) -> own stde::cell_nat::CellNat<> {
 * let *r = stde::cell_nat::CellNat<>{*v};
 * return r;
 * }
 */
struct CellNat* new(unsigned int* ov)
//@requires u_integer_own(ov, ?v);
//@ensures  CellNat_own(result, v);
{
	struct CellNat* c = malloc(sizeof(struct CellNat));
	if(c == 0) abort();
	c->value = *ov;
	free(ov);
	return c;
}

/***
 * pub safe fn stde::cell_nat::get<alpha|>(this: immut'alpha stde::cell_nat::CellNat<>) -> own nat {
 * let {*imm_value} = *this;
 * let *r = copy *imm_value;
 * drop imm_value;
 * return r;
 * }
 */
unsigned int* get(struct CellNat* c)
//@ requires CellNat_shr(c,?v);
//@ ensures u_integer_own(result, v);
{
	unsigned int* r = malloc(sizeof(unsigned int));
	if(r == 0) abort();
	*r = c->value;
	return r;
}

/*
pub fn set<'a>(this: &'a CellNat, v: u32) -> () {
    let imm_value = &this.value;
    let ptr_value = imm_value as *const u32 as *mut u32;
    let mut_value = unsafe { &mut *ptr_value };
    dbg!(imm_value); // imm_value and mut_value are alive together
    *mut_value = v;
}
*/
/***
 * pub safe fn stde::cell_nat::set<alpha|>(this: immut'alpha stde::cell_nat::CellNat<>, v: own nat) -> own unit {
 * // producing parameters
 * {{sstore=this:#this,v:#v; sheap=alpha::[shr(#fr)]#this->stde::cell_nat::CellNat<>,[del]#v->nat(#value)}}
 *
 * let {*imm_value} = this; //type access check is performed at type checking
 * // pointer calculation and openning the type predicate
 * // alpha::[shr(fr)]this->stde::cell_nat::CellNat<> =* alpha::[shr(1.0)]this->nat(value) *
 * No active path to #this with type nat unless frozen by alpha
 * {{sstore=this:#this,v:#v,imm_value:#this; sheap=[del]#v->nat(#value),alpha::[shr(1.0)]#this->nat(#value1)}}
 *
 * let ptr_value = raw imm_value;
 * {{sstore=this:#this,v:#v,imm_value:#this,ptr_value:#this;
 * sheap=alpha::[shr(#fr)]#this->stde::cell_nat::CellNat<>,[del]#v->#value}}
 *
 * unsafe;
 * intro beta;
 * let mut_value = mutbor'beta ptr_value;
 *
 * safe;
 * swap(*mut_value, *v);
 * drop mut_value;
 * now beta;
 * drop ptr_value;
 * drop imm_value;
 * drop v;
 * let *r = unit<>{};
 * return r;
 * }
 */
