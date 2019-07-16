#include "stdlib.h"

struct C {
  int x;
};

struct C* create_C(int x) 
  //@ requires emp;
  //@ ensures result->x |-> x &*& malloc_block_C(result);
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

/*@

predicate counter(struct C* c, int x, int id, real frac, int nbTickets);

predicate ticket(struct C* c, int id, real frac);

lemma void create_counter(struct C* c);
  requires [?f]c->x |-> ?x;
  ensures counter(c, x, ?id, f, 0);

lemma void create_ticket(struct C* c);
  requires counter(c, ?x, ?id, ?f, ?i);
  ensures counter(c, x, id, f, i + 1) &*& ticket(c, id, ?f2) &*& [f2]c->x |-> x;

lemma void dispose_ticket(struct C* c);
  requires counter(c, ?x, ?id, ?f, ?i) &*& ticket(c, id, ?f2) &*& [f2]c->x |-> x;
  ensures counter(c, x, id, f, i - 1);

lemma void dispose_counter(struct C* c);
  requires counter(c, ?x, ?id, ?f, 0);
  ensures [f]c->x |-> x;
@*/

bool random();
//@ requires emp;
//@ ensures emp;

int main() 
  //@ requires emp;
  //@ ensures emp;
{
  struct C* c = create_C(5);
  //@ create_counter(c);
  //@ assert counter(c, 5, ?id, 1, 0);
  bool b = random();
  int n = 0;
  //@ close tickets(c, 5, id, 0);
  // split of an arbitrary number of children
  while(b) 
    //@ invariant 0<=n &*& counter(c, 5, id, 1, n) &*& tickets(c, 5, id, n);
  {
    //@ create_ticket(c);
    n = n + 1;
    //@ close tickets(c, 5, id, n);
    b = random();
  }

  // put the permission back together
  while(0<n) 
    //@ invariant 0<=n &*& counter(c, 5, id, 1, n) &*& tickets(c, 5, id, n);
  {
    //@ open tickets(c, 5, id, n);
    //@ dispose_ticket(c);
    n = n - 1;
  }
  //@ open tickets(c, 5, id, 0);
  //@ dispose_counter(c);
  free(c);
  return 0;
}

int main2()
//@ requires emp;
//@ ensures emp;
{
  struct C* c = create_C(3);
// { [1]c->x |-> 3 }
  //@ create_counter(c);
// { mother(c, 3, id, 1, 0) }
  //@ create_ticket(c);
// { mother(c, 3, id, 1, 1) * child(c, id, f) * [f]c->x |->3 }
//...
  //@ dispose_ticket(c);
// { mother(c, 3, id, 1, 0) }
  //@ dispose_counter(c);
// { [1]c->x |-> 3 }
  free(c);
  return 0;
}

/*@
predicate tickets(struct C* c, int x, int id, int howMany) =
  howMany <= 0 ? emp : ticket(c, id, ?f) &*& [f]c->x |-> x &*& tickets(c, x, id, howMany - 1);
@*/
