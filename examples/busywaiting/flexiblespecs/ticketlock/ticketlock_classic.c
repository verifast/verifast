// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

//@ #include <quantifiers.gh>
#include <stdlib.h>
#include "ticketlock.h"
#include "ticketlock_classic.h"

/*@

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
      signal(nth(owner, signals), sublevel(level, {0}), false)
  :
      inv();

predicate ticketlock_classic(ticketlock_classic lock; level level, predicate() inv) =
  malloc_block_ticketlock_classic(lock) &*&
  lock->level |-> level &*& ticketlock_classic_nb_level_dims <= level_subspace_nb_dims(level) &*&
  lock->inv_ |-> inv &*&
  lock->signalsBox |-> ?signalsBox &*&
  lock->lock |-> ?lock0 &*& ticketlock(lock0, sublevel(level, {1}), ticketlock_classic_inv(level, inv, signalsBox));

@*/

ticketlock_classic create_ticketlock_classic()
/*@
requires
    exists<pair<level, predicate()> >(pair(?level, ?inv)) &*&
    ticketlock_classic_nb_level_dims <= level_subspace_nb_dims(level) &*&
    inv();
@*/
//@ ensures ticketlock_classic(result, level, inv);
{
  //@ open exists(_);
  ticketlock_classic result = malloc(sizeof(struct ticketlock_classic));
  if (result == 0) abort();
  //@ result->level = level;
  //@ result->inv_ = inv;
  //@ create_box signalsBox = growing_list({});
  //@ result->signalsBox = signalsBox;
  //@ close ticketlock_classic_inv(level, inv, signalsBox)(0, false);
  //@ close exists(pair(sublevel(level, {1}), ticketlock_classic_inv(level, inv, signalsBox)));
  //@ assert level == level(?levelFunc, cons(?localLevel_max_length, ?localLevel0));
  ticketlock lock = create_ticketlock();
  result->lock = lock;
  //@ close ticketlock_classic(result, level, inv);
  return result;
}

/*@

predicate ticketlock_classic_held(ticketlock_classic lock, level level, predicate() inv, real f, pair<void *, level> ob) =
  [f]malloc_block_ticketlock_classic(lock) &*&
  [f]lock->level |-> level &*& ticketlock_classic_nb_level_dims <= level_subspace_nb_dims(level) &*&
  [f]lock->inv_ |-> inv &*&
  [f]lock->signalsBox |-> ?signalsBox &*&
  [f]lock->lock |-> ?lock0 &*& ticketlock_held(lock0, sublevel(level, {1}), ticketlock_classic_inv(level, inv, signalsBox), f, ?ticket) &*&
  has_at(_, signalsBox, ticket, ?signal) &*& ob == pair(signal, sublevel(level, {0}));

@*/
void ticketlock_classic_acquire(ticketlock_classic lock)
//@ requires obs(?p, ?obs) &*& [?f]ticketlock_classic(lock, ?level, ?inv) &*& forall(map(snd, obs), (all_sublevels_lt)(ticketlock_classic_nb_level_dims, level)) == true;
//@ ensures obs(?p1, cons(?ob, obs)) &*& is_ancestor_of(p, p1) == true &*& ticketlock_classic_held(lock, level, inv, f, ob) &*& inv() &*& level_lt(level, level_of(ob)) == true;
{
  //@ open ticketlock_classic(lock, level, inv);
  //@ box signalsBox = lock->signalsBox;
  //@ assert level == level(?levelFunc, cons(?level_max_length, ?level0));
  //@ int acquireThread = currentThread;
  {
    /*@
    predicate wait_inv(int owner, void *func, list<pathcomp> p1) =
      is_ancestor_of(p, p1) == true &*&
      owner == -1 ?
        true
      :
        has_at(_, signalsBox, owner, ?signal) &*& wait_perm(?p0, signal, sublevel(level, {0}), func) &*& is_ancestor_of(p0, p1) == true;
    predicate post(int ticket) =
      has_at(_, signalsBox, ticket, ?signal) &*&
      obs(?p1, cons(pair(signal, sublevel(level, {0})), obs)) &*&
      is_ancestor_of(p, p1) == true &*&
      inv();
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(sublevel(level, {1}), ticketlock_classic_inv(level, inv, signalsBox), wait_inv, currentThread)(func) {
      assert obs(?p1, ?obs1);
      open wait_inv(?owner0, ?func0, ?p0);
      open ticketlock_classic_inv(level, inv, signalsBox)(?owner, true);
      assert growing_list(signalsBox, ?signals);
      if (owner0 != -1) {
        consuming_box_predicate growing_list(signalsBox, signals)
        consuming_handle_predicate has_at(?handleId, owner0, ?signal0)
        perform_action noop() {}
        producing_box_predicate growing_list(signals)
        producing_handle_predicate has_at(handleId, owner0, signal0);
        assert wait_perm(?p00, signal0, sublevel(level, {0}), func0);
        is_ancestor_of_trans(p00, p0, p1);
      }
      if (owner0 != owner) {
        if (0 <= owner0) {
          leak has_at(_, signalsBox, owner0, ?signal0) &*& wait_perm(_, signal0, sublevel(level, {0}), func0);
        }
        consuming_box_predicate growing_list(signalsBox, signals)
        perform_action noop() {}
        producing_box_predicate growing_list(signals)
        producing_fresh_handle_predicate has_at(owner, nth(owner, signals));
        create_wait_perm(nth(owner, signals), sublevel(level, {0}), func);
        is_ancestor_of_refl(p1);
      }
      if (!forall(map(snd, obs1), (level_lt)(sublevel(level, {0})))) {
          level badLevel = not_forall(map(snd, obs1), (level_lt)(sublevel(level, {0})));
          forall_elim(map(snd, obs1), (level_lt)(sublevel(level, {1})), badLevel);
          assert badLevel == level(_, cons(level_max_length, ?badLevel0));
          lex0_lt_append(level_max_length, level0, {0}, {1});
          lex0_lt_trans(level_max_length, append(level0, {0}), append(level0, {1}), badLevel0);
          assert false;
      }
      wait(nth(owner, signals));
      close ticketlock_classic_inv(level, inv, signalsBox)(owner, true);
      is_ancestor_of_trans(p, p0, p1);
      close wait_inv(owner, func, p1);
    };
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(obs, sublevel(level, {1}), ticketlock_classic_inv(level, inv, signalsBox), wait_inv, post, currentThread)() {
      open wait_inv(?owner0, ?func0, ?p0);
      close wait_inv(owner0, func0, p0);
      leak wait_inv(owner0, func0, p0);
      assert obs_(acquireThread, ?p1, _);
      open ticketlock_classic_inv(level, inv, signalsBox)(?owner, false);
      void *signal = create_signal();
      init_signal(signal, sublevel(level, {0}));
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
    //@ close wait_inv(-1, 0, p);
    /*@
    if (!forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, sublevel(level, {1})))) {
        level badLevel = not_forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, sublevel(level, {1})));
        forall_elim(map(snd, obs), (all_sublevels_lt)(ticketlock_classic_nb_level_dims, level), badLevel);
        assert badLevel == level(_, cons(level_max_length, ?badLevel0));
        lex0_subspace_lt_append_l(level0, {1}, badLevel0);
        assert false;
    }
    @*/
    ticketlock_acquire(lock->lock);
    //@ open post(?ticket);
  }
  //@ assert has_at(_, signalsBox, ?ticket, ?signal);
  //@ close ticketlock_classic_held(lock, level, inv, f, pair(signal, sublevel(level, {0})));
  //@ lex0_lt_append(level_max_length, level0, {}, {0});
}

void ticketlock_classic_release(ticketlock_classic lock)
//@ requires obs(?p, ?obs) &*& ticketlock_classic_held(lock, ?level, ?inv, ?f, ?ob) &*& mem(ob, obs) == true &*& inv();
//@ ensures obs(p, remove(ob, obs)) &*& [f]ticketlock_classic(lock, level, inv);
{
  //@ open ticketlock_classic_held(lock, level, inv, f, ob);
  //@ box signalsBox = lock->signalsBox;
  //@ assert has_at(?handleId, signalsBox, ?ticket, ?signal);
  {
    /*@
    predicate pre() =
      obs(p, obs) &*& has_at(handleId, signalsBox, ticket, signal) &*& inv();
    predicate post() =
      obs(p, remove(ob, obs));
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_release_ghost_op(ticketlock_classic_inv(level, inv, signalsBox), ticket, pre, post)() {
      open pre();
      open ticketlock_classic_inv(level, inv, signalsBox)(ticket, true);
      consuming_box_predicate growing_list(signalsBox, ?signals)
      consuming_handle_predicate has_at(handleId, ticket, signal)
      perform_action noop() {}
      producing_box_predicate growing_list(signals);
      set_signal(signal);
      leak signal(signal, sublevel(level, {0}), true);
      close ticketlock_classic_inv(level, inv, signalsBox)(ticket + 1, false);
      close post();
    };
    @*/
    //@ close pre();
    ticketlock_release(lock->lock);
    //@ open post();
  }
}

void ticketlock_classic_dispose(ticketlock_classic lock)
//@ requires ticketlock_classic(lock, ?level, ?inv);
//@ ensures inv();
{
  ticketlock_dispose(lock->lock);
  //@ box signalsBox = lock->signalsBox;
  free(lock);
  //@ open ticketlock_classic_inv(level, inv, signalsBox)(_, _);
  //@ leak growing_list(signalsBox, _);
}
