#include <stdlib.h>

/*@

predicate counting(int id, int nbTickets, real ticketsTotalFrac);
predicate ticket(int countingId, real frac);

lemma int create_counting(real initFrac);
    requires true;
    ensures counting(result, 1, initFrac) &*& ticket(result, initFrac);

lemma void counting_split_ticket();
    requires counting(?id, ?count, ?totalFrac) &*& ticket(id, ?f);
    ensures 1 <= count &*& counting(id, count + 1, totalFrac) &*& ticket(id, f/2) &*& ticket(id, f/2);

lemma void counting_destroy_ticket();
    requires counting(?id, ?count, ?totalFrac) &*& ticket(id, ?f);
    ensures count > 0 &*& counting(id, count - 1, totalFrac - f);

lemma void counting_done();
    requires counting(?id, ?count, ?totalFrac) &*& count == 0;
    ensures counting(id, count, totalFrac) &*& totalFrac == 0;

@*/

/*@

predicate Acq(predicate() P); // P will be available after the next acquire fence

predicate relaxed_ullong(unsigned long long *p; predicate(unsigned long long) inv);
predicate relaxed_ullong_tied_resource(unsigned long long *p, predicate() P);

lemma void create_relaxed_ullong(unsigned long long *p, predicate(unsigned long long) inv, predicate() P);
    requires *p |-> ?v0 &*& inv(v0) &*& v0 <= 1 &*& P(); // Small initial value, so that it cannot overflow
    ensures relaxed_ullong(p, inv) &*& relaxed_ullong_tied_resource(p, P);

lemma void destroy_relaxed_ullong(unsigned long long *p);
    requires relaxed_ullong(p, ?inv);
    ensures *p |-> ?v &*& inv(v);

predicate_ctor sep(predicate() P, predicate() Q)() = P() &*& Q();

lemma void relaxed_ullong_tied_resource_separate(predicate() P, predicate() Q);
    requires relaxed_ullong_tied_resource(?p, sep(P, Q));
    ensures relaxed_ullong_tied_resource(p, P) &*& relaxed_ullong_tied_resource(p, Q);

@*/

/*@

typedef lemma void fetch_and_increment_relaxed_ghop(predicate(unsigned long long) inv, predicate() P, predicate() Q)();
    requires inv(?v) &*& P();
    ensures inv(v + 1) &*& Q();

@*/

void fetch_and_increment_relaxed(unsigned long long *p);
/*@
requires
    [?f]relaxed_ullong(p, ?inv) &*& relaxed_ullong_tied_resource(p, ?P) &*&
    is_fetch_and_increment_relaxed_ghop(?ghop, inv, P, ?Q);
@*/
/*@
ensures
    [f]relaxed_ullong(p, inv) &*& relaxed_ullong_tied_resource(p, Q);
@*/

/*@

typedef lemma void fetch_and_decrement_release_ghop(real f, unsigned long long *p, predicate(unsigned long long) inv, predicate() P, predicate() pre, fixpoint(unsigned long long, predicate()) post)();
    requires [f]relaxed_ullong(p, inv) &*& inv(?v) &*& P() &*& pre();
    ensures 1 <= v &*& inv(v - 1) &*& (post(v))();

@*/

unsigned long long fetch_and_decrement_release(unsigned long long *p);
/*@
requires
    [?f]relaxed_ullong(p, ?inv) &*& relaxed_ullong_tied_resource(p, ?P) &*&
    is_fetch_and_decrement_release_ghop(?ghop, f, p, inv, P, ?pre, ?post) &*& pre();
@*/
//@ ensures Acq(post(result));

void fence_acquire();
//@ requires Acq(?P);
//@ ensures P();

struct arc {
  unsigned long long counter;
  int payload;
};

typedef struct arc *arc;

/*@

predicate_ctor arc_inv(arc arc, int countingId)(unsigned long long count) =
    counting(countingId, count, ?totalFrac) &*&
    count == 0 ?
        true
    :
        malloc_block_arc(arc) &*&
        totalFrac == 1 ?
            true
        :
            [1 - totalFrac]relaxed_ullong(&arc->counter, arc_inv(arc, countingId)) &*&
            [1 - totalFrac]arc->payload |-> _;

predicate_ctor ticket_(int countingId, real f)() = ticket(countingId, f);

predicate arc(arc arc, int payload) =
    exists<pair<real, int> >(pair(?f, ?countingId)) &*&
    [f]relaxed_ullong(&arc->counter, arc_inv(arc, countingId)) &*&
    [f]arc->payload |-> payload &*&
    relaxed_ullong_tied_resource(&arc->counter, ticket_(countingId, f));

@*/

arc create_arc(int payload)
//@ requires true;
//@ ensures arc(result, payload);
{
  arc result = malloc(sizeof(struct arc));
  if (result == 0) abort();
  result->counter = 1;
  result->payload = payload;
  return result;
  //@ int countingId = create_counting(1);
  //@ close exists(pair(1r, countingId));
  //@ close arc_inv(result, countingId)(1);
  //@ close ticket_(countingId, 1)();
  //@ create_relaxed_ullong(&result->counter, arc_inv(result, countingId), ticket_(countingId, 1));
  //@ close arc(result, payload);
}

int arc_get_payload(arc arc)
//@ requires arc(arc, ?payload);
//@ ensures arc(arc, payload) &*& result == payload;
{
  //@ open arc(arc, payload);
  return arc->payload;
  //@ close arc(arc, payload);
}

void arc_clone(arc arc)
//@ requires arc(arc, ?payload);
//@ ensures arc(arc, payload) &*& arc(arc, payload);
{
  //@ open arc(arc, payload);
  //@ open exists(pair(?f, ?countingId));
  /*@
  produce_lemma_function_pointer_chunk fetch_and_increment_relaxed_ghop(arc_inv(arc, countingId), ticket_(countingId, f), sep(ticket_(countingId, f/2), ticket_(countingId, f/2)))() {
    open arc_inv(arc, countingId)(?v);
    open ticket_(countingId, f)();
    counting_split_ticket();
    close ticket_(countingId, f/2)();
    close ticket_(countingId, f/2)();
    close sep(ticket_(countingId, f/2), ticket_(countingId, f/2))();
    close arc_inv(arc, countingId)(v + 1);
  };
  @*/
  fetch_and_increment_relaxed(&arc->counter);
  //@ relaxed_ullong_tied_resource_separate(ticket_(countingId, f/2), ticket_(countingId, f/2));
  //@ close exists(pair(f/2, countingId));
  //@ close exists(pair(f/2, countingId));
  //@ close arc(arc, payload);
  //@ close arc(arc, payload);
}

/*@

predicate_ctor arc_post(real f, arc arc, int countingId, unsigned long long count)() =
    count == 1 ?
        relaxed_ullong(&arc->counter, arc_inv(arc, countingId)) &*&
        malloc_block_arc(arc) &*&
        arc->payload |-> _
    :
        true;

@*/

void arc_drop(arc arc)
//@ requires arc(arc, ?payload);
//@ ensures true;
{
  //@ open arc(arc, payload);
  //@ open exists(pair(?f, ?countingId));
  {
    //@ predicate pre() = [f]arc->payload |-> _;
    /*@
    produce_lemma_function_pointer_chunk fetch_and_decrement_release_ghop(f, &arc->counter, arc_inv(arc, countingId), ticket_(countingId, f), pre, (arc_post)(f, arc, countingId))() {
      open arc_inv(arc, countingId)(?count);
      open ticket_(countingId, f)();
      open pre();
      counting_destroy_ticket();
      if (count == 1)
          counting_done();
      close arc_post(f, arc, countingId, count)();
      close arc_inv(arc, countingId)(count - 1);
    };
    @*/
    //@ close pre();
    unsigned long long counter0 = fetch_and_decrement_release(&arc->counter);
    if (counter0 == 1) {
      fence_acquire();
      //@ open arc_post(f, arc, countingId, 1)();
      //@ destroy_relaxed_ullong(&arc->counter);
      //@ leak arc_inv(arc, countingId)(_);
      free(arc);
    }
    //@ if (counter0 != 1) leak Acq(_);
  }
}
