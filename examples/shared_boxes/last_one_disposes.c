#include "gotsmanlock.h"
#include "stdlib.h"

struct packet {
  int lock;
  int count;
  void* data;
};

//@ fixpoint real frac(int x, int y);

/*@ 
lemma_auto void frac_same(int x);
  requires x != 0;
  ensures frac(x, x) == 1r;
  
lemma void frac_same_denom(int x, int y, int M);
  requires M != 0;
  ensures frac(x, M) + frac(y, M) == frac(x + y, M);
@*/   

/*@
predicate_ctor lock_inv(struct packet* p, int M)() = malloc_block_packet(p) &*& p->count |-> ?X &*& 0 <= X &*& p->data |-> _ &*& X == 0 ? true : [frac(X, M)]lock(&p->lock, lock_inv(p, M)); 
@*/

struct packet* create_packet(int M)
  //@ requires 0 < M;
  //@ ensures lock(&result->lock, lock_inv(result, M));
{
  struct packet* p = malloc(sizeof(struct packet));
  if(p == 0) abort();
  p->count = 0;
  //@ close exists<predicate()>(lock_inv(p, M));
  init(&p->lock);
  //@ close lock_inv(p, M)();
  release(&p->lock);
  return p;
}

void thread(struct packet* p, int M)
  //@ requires [frac(1, M)]lock(&p->lock, lock_inv(p, M)) &*& 0 < M;
  //@ ensures true;
{
  acquire(&p->lock);
  //@ open lock_inv(p, M)();
  p->count++;
  if(p->count == M) {
    //@ int X = p->count - 1;
    /*@
    if(M > 1) {
      frac_same_denom(1, X, M);
      merge_fractions lock(&p->lock, lock_inv(p, M));
    }
    @*/
    finalize(&p->lock);
    free(p);
  } else {
    //@ close lock_inv(p, M)();
    release(&p->lock);
  }
}