// tab_size:2

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

//@ #include <quantifiers.gh>
#include <stdlib.h>
#include "ticketlock.h"
#include "ticketlock_classic.h"

/*@

lemma a mem_map_mem<a, b>(b y, list<a> xs, fixpoint(a, b) f)
    requires mem(y, map(f, xs)) == true;
    ensures mem(result, xs) == true &*& f(result) == y;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (f(x) == y)
                return x;
            else
                return mem_map_mem(y, xs0, f);
    }
}

box_class growing_list(list<void *> xs) {
  invariant true;
  action noop();
    requires true;
    ensures xs == old_xs;
  action add(void *elem);
    requires true;
    ensures xs == append(old_xs, {elem});
  handle_predicate has_at(int k, void *x) {
    invariant 0 <= k && k < length(xs) && nth(k, xs) == x;
    preserved_by noop() {}
    preserved_by add(elem) {
      nth_append(old_xs, {elem}, k);
    }
  }
}

@*/

struct ticketlock_classic {
  //@ level level;
  //@ predicate() inv_;
  //@ box signalsBox;
  ticketlock lock;
};

/*@

predicate_ctor ticketlock_classic_inv(level level, predicate() inv, box signalsBox)(int owner, bool held) =
  growing_list(signalsBox, ?signals) &*&
  0 <= owner &*&
  length(signals) == (held ? owner + 1 : owner) &*&
  held ?
      signal(nth(owner, signals), level, false)
  :
      inv();

predicate ticketlock_classic(ticketlock_classic lock; level level, predicate() inv) =
  malloc_block_ticketlock_classic(lock) &*&
  lock->level |-> level &*& func_lt_level(ticketlock_classic_acquire, level) == true &*&
  lock->inv_ |-> inv &*&
  lock->signalsBox |-> ?signalsBox &*&
  lock->lock |-> ?lock0 &*& ticketlock(lock0, ticketlock_classic_inv(level, inv, signalsBox));

@*/

ticketlock_classic create_ticketlock_classic()
//@ requires exists<pair<level, predicate()> >(pair(?level, ?inv)) &*& func_lt_level(ticketlock_classic_acquire, level) == true &*& inv();
//@ ensures ticketlock_classic(result, level, inv);
//@ terminates;
{
  //@ open exists(_);
  ticketlock_classic result = malloc(sizeof(struct ticketlock_classic));
  if (result == 0) abort();
  //@ result->level = level;
  //@ result->inv_ = inv;
  //@ create_box signalsBox = growing_list({});
  //@ result->signalsBox = signalsBox;
  //@ close ticketlock_classic_inv(level, inv, signalsBox)(0, false);
  //@ close exists(ticketlock_classic_inv(level, inv, signalsBox));
  ticketlock lock = create_ticketlock();
  result->lock = lock;
  //@ close ticketlock_classic(result, level, inv);
  return result;
}

/*@

predicate ticketlock_classic_held(ticketlock_classic lock, level level, predicate() inv, real f, pair<void *, level> ob) =
  [f]malloc_block_ticketlock_classic(lock) &*&
  [f]lock->level |-> level &*& func_lt_level(ticketlock_classic_acquire, level) == true &*&
  [f]lock->inv_ |-> inv &*&
  [f]lock->signalsBox |-> ?signalsBox &*&
  [f]lock->lock |-> ?lock0 &*& ticketlock_held(lock0, ticketlock_classic_inv(level, inv, signalsBox), f, ?ticket) &*&
  has_at(_, signalsBox, ticket, ?signal) &*& ob == pair(signal, level);

@*/
void ticketlock_classic_acquire(ticketlock_classic lock)
//@ requires obs(?p, ?obs) &*& [?f]ticketlock_classic(lock, ?level, ?inv) &*& forall(map(snd, obs), (level_lt)(level)) == true;
//@ ensures obs(?p1, cons(?ob, obs)) &*& is_ancestor_of(p, p1) == true &*& ticketlock_classic_held(lock, level, inv, f, ob) &*& inv() &*& level_of(ob) == level;
//@ terminates;
{
  //@ open ticketlock_classic(lock, level, inv);
  //@ box signalsBox = lock->signalsBox;
  //@ int acquireThread = currentThread;
  //@ produce_func_lt(ticketlock_acquire);
  /*@
  if (!forall(map(snd, obs), (func_lt_level)(ticketlock_acquire))) {
      level badLevel = not_forall(map(snd, obs), (func_lt_level)(ticketlock_acquire));
      forall_elim(map(snd, obs), (level_lt)(level), badLevel);
      assert false;
  }
  @*/
  {
    /*@
    predicate wait_inv(int owner, list<int> M, list<pathcomp> p1, list<pair<void *, level> > obs1) =
      obs1 == obs &*&
      is_ancestor_of(p, p1) == true &*&
      owner == -1 ?
        call_below_perm_(currentThread, ticketlock_classic_acquire)
      :
        call_below_perm_lex(?p0, ticketlock_classic_acquire, M) &*&
        has_at(_, signalsBox, owner, ?signal) &*& wait_perm(p0, signal, level, ticketlock_acquire) &*& is_ancestor_of(p0, p1) == true;
    predicate post(int ticket) =
      has_at(_, signalsBox, ticket, ?signal) &*&
      obs(?p1, cons(pair(signal, level), obs)) &*&
      is_ancestor_of(p, p1) == true &*&
      inv();
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(ticketlock_classic_inv(level, inv, signalsBox), wait_inv, currentThread)(M) {
      assert obs(?p1, ?obs1);
      open wait_inv(?owner0, ?M0, ?p0, _);
      open ticketlock_classic_inv(level, inv, signalsBox)(?owner, true);
      assert growing_list(signalsBox, ?signals);
      if (owner0 != -1) {
        consuming_box_predicate growing_list(signalsBox, signals)
        consuming_handle_predicate has_at(?handleId, owner0, ?signal0)
        perform_action noop() {}
        producing_box_predicate growing_list(signals)
        producing_handle_predicate has_at(handleId, owner0, signal0);
        assert wait_perm(?p00, signal0, level, ticketlock_acquire);
        is_ancestor_of_trans(p00, p0, p1);
      }
      if (owner0 == -1 || lexprod_lt(M, M0)) {
        if (0 <= owner0) {
          leak has_at(_, signalsBox, owner0, ?signal0) &*& wait_perm(_, signal0, level, ticketlock_acquire);
          call_below_perm_lex_weaken(M);
        } else {
          pathize_call_below_perm__lex(M);
        }
        consuming_box_predicate growing_list(signalsBox, signals)
        perform_action noop() {}
        producing_box_predicate growing_list(signals)
        producing_fresh_handle_predicate has_at(owner, nth(owner, signals));
        create_wait_perm(nth(owner, signals), level, ticketlock_acquire);
        is_ancestor_of_refl(p1);
      }
      wait(nth(owner, signals));
      close ticketlock_classic_inv(level, inv, signalsBox)(owner, true);
      is_ancestor_of_trans(p, p0, p1);
      close wait_inv(owner, M, p1, obs);
    };
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(ticketlock_classic_inv(level, inv, signalsBox), wait_inv, post, currentThread)() {
      open wait_inv(?owner0, ?M0, ?p0, _);
      close wait_inv(owner0, M0, p0, obs);
      leak wait_inv(owner0, M0, p0, _);
      assert obs_(acquireThread, ?p1, _);
      open ticketlock_classic_inv(level, inv, signalsBox)(?owner, false);
      void *signal = create_signal();
      init_signal(signal, level);
      consuming_box_predicate growing_list(signalsBox, ?signals)
      perform_action add(signal) {
        nth_append_r(signals, {signal}, 0);
      }
      producing_box_predicate growing_list(append(signals, {signal}))
      producing_fresh_handle_predicate has_at(owner, signal);
      close ticketlock_classic_inv(level, inv, signalsBox)(owner, true);
      is_ancestor_of_trans(p, p0, p1);
      close post(owner);
    };
    @*/
    //@ is_ancestor_of_refl(p);
    //@ produce_call_below_perm_();
    //@ close wait_inv(-1, {}, p, obs);
    ticketlock_acquire(lock->lock);
    //@ open post(?ticket);
  }
  //@ assert has_at(_, signalsBox, ?ticket, ?signal);
  //@ close ticketlock_classic_held(lock, level, inv, f, pair(signal, level));
}

void ticketlock_classic_release(ticketlock_classic lock)
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire)) == true &*&
    ticketlock_classic_held(lock, ?level, ?inv, ?f, ?ob) &*& mem(ob, obs) == true &*& inv();
@*/
//@ ensures obs(?p1, remove(ob, obs)) &*& [f]ticketlock_classic(lock, level, inv) &*& is_ancestor_of(p, p1) == true;
//@ terminates;
{
  //@ open ticketlock_classic_held(lock, level, inv, f, ob);
  //@ box signalsBox = lock->signalsBox;
  //@ assert has_at(?handleId, signalsBox, ?ticket, ?signal);
  {
    /*@
    predicate pre() =
      has_at(handleId, signalsBox, ticket, signal) &*& inv();
    predicate post(list<pathcomp> p1, list<pair<void *, level> > obs1) =
      is_ancestor_of(p, p1) == true &*&
      obs1 == remove(ob, obs);
    @*/
    //@ produce_func_lt(ticketlock_acquire);
    /*@
    produce_lemma_function_pointer_chunk ticketlock_release_ghost_op(ticketlock_classic_inv(level, inv, signalsBox), ticket, p, obs, pre, post, currentThread)() {
      open pre();
      open ticketlock_classic_inv(level, inv, signalsBox)(ticket, true);
      consuming_box_predicate growing_list(signalsBox, ?signals)
      consuming_handle_predicate has_at(handleId, ticket, signal)
      perform_action noop() {}
      producing_box_predicate growing_list(signals);
      set_signal(signal);
      leak signal(signal, level, true);
      close ticketlock_classic_inv(level, inv, signalsBox)(ticket + 1, false);
      assert obs_(_, ?p1, ?obs1);
      close post(p1, obs1);
      if (!forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire))) {
        level badLevel = not_forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire));
        assert mem(badLevel, map(snd, obs1)) == true;
        pair<void *, level> badOb = mem_map_mem(badLevel, obs1, snd);
        assert mem(badOb, obs1) == true;
        mem_remove_mem(badOb, ob, obs);
        assert mem(badOb, obs) == true;
        mem_map(badOb, obs, snd);
        forall_elim(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire), snd(badOb));
        assert false;
      }
    };
    @*/
    /*@
    if (!forall(map(snd, obs), (func_lt_level)(ticketlock_acquire))) {
        level badLevel = not_forall(map(snd, obs), (func_lt_level)(ticketlock_acquire));
        forall_elim(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire), badLevel);
        assert false;
    }
    @*/
    //@ close pre();
    ticketlock_release(lock->lock);
    //@ open post(?p1, _);
    //@ assert obs(?p2, _);
    //@ is_ancestor_of_trans(p, p1, p2);
  }
}

void ticketlock_classic_dispose(ticketlock_classic lock)
//@ requires ticketlock_classic(lock, ?level, ?inv);
//@ ensures inv();
//@ terminates;
{
  ticketlock_dispose(lock->lock);
  //@ box signalsBox = lock->signalsBox;
  free(lock);
  //@ open ticketlock_classic_inv(level, inv, signalsBox)(_, _);
  //@ leak growing_list(signalsBox, _);
}
