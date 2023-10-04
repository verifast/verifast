// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "spinlock.h"
//@ #include <quantifiers.gh>

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

typedef struct spinlock_classic {
  spinlock_t spinlock;
  //@ level level;
  //@ predicate(int, bool) inv_;
  //@ int acquireCredits;
  //@ list<void *> signals;
  //@ box signalsBox;
} *spinlock_classic_t;

/*@

predicate_ctor spinlock_classic_inv(spinlock_classic_t spinlock, level level, predicate(int, bool) inv, int acquireCredits, box signalsBox)(bool locked) =
    growing_list(signalsBox, ?signals) &*& length(signals) <= acquireCredits &*&
    [1/2]spinlock->signals |-> signals &*&
    inv(acquireCredits - length(signals), locked) &*&
    locked ? 1 <= length(signals) &*& signal(nth(length(signals) - 1, signals), level, false) : [1/2]spinlock->signals |-> signals;

predicate spinlock_classic(spinlock_classic_t spinlock; level level, predicate(int, bool) inv) =
    malloc_block_spinlock_classic(spinlock) &*&
    spinlock->spinlock |-> ?spinlock_ &*& spinlock->level |-> level &*& spinlock->inv_ |-> inv &*&
    spinlock->acquireCredits |-> ?acquireCredits &*&
    spinlock->signalsBox |-> ?signalsBox &*& 
    spinlock(spinlock_, spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox));

@*/

spinlock_classic_t create_spinlock_classic()
/*@
requires
    exists<pair<level, pair<predicate(int, bool), int> > >(pair(?level, pair(?inv, ?acquireCredits))) &*&
    0 <= acquireCredits &*& inv(acquireCredits, false);
@*/
//@ ensures spinlock_classic(result, level, inv);
{
  spinlock_classic_t result = malloc(sizeof(struct spinlock_classic));
  if (result == 0) abort();
  //@ result->acquireCredits = acquireCredits;
  //@ result->level = level;
  //@ result->inv_ = inv;
  //@ create_box signalsBox = growing_list({});
  //@ result->signalsBox = signalsBox;
  //@ result->signals = nil;
  //@ close spinlock_classic_inv(result, level, inv, acquireCredits, signalsBox)(false);
  //@ close exists(spinlock_classic_inv(result, level, inv, acquireCredits, signalsBox));
  result->spinlock = create_spinlock();
  return result;
  //@ close spinlock_classic(result, level, inv);
}

/*@

typedef lemma void spinlock_classic_acquire_ghost_op(predicate(int, bool) inv, predicate() pre, predicate() post)();
    requires inv(?acquireCredits, false) &*& pre() &*& atomic_spaces(?spaces) &*& forall(spaces, (space_name_lt)(spinlock_classic_acquire)) == true;
    ensures inv(acquireCredits - 1, true) &*& post() &*& 1 <= acquireCredits &*& atomic_spaces(spaces);

predicate spinlock_classic_held(spinlock_classic_t spinlock, real f, predicate(int, bool) inv, pair<void *, level> ob) =
    [f]malloc_block_spinlock_classic(spinlock) &*&
    [f]spinlock->spinlock |-> ?spinlock_ &*& [f]spinlock->level |-> ?level &*& [f]spinlock->inv_ |-> inv &*&
    [f]spinlock->acquireCredits |-> ?acquireCredits &*&
    [f]spinlock->signalsBox |-> ?signalsBox &*& 
    [f]spinlock(spinlock_, spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)) &*&
    [1/2]spinlock->signals |-> ?signals &*& 0 < length(signals) &*&
    ob == pair(nth(length(signals) - 1, signals), level);

@*/

void spinlock_classic_acquire(spinlock_classic_t spinlock)
/*@
requires
    obs(?p, ?obs) &*& [?f]spinlock_classic(spinlock, ?level, ?inv) &*& is_spinlock_classic_acquire_ghost_op(?ghop, inv, ?pre, ?post) &*& pre() &*&
    forall(map(snd, obs), (level_lt)(level)) == true;
@*/
//@ ensures obs(p, cons(?ob, obs)) &*& spinlock_classic_held(spinlock, f, inv, ob) &*& post() &*& level_of(ob) == level;
{
  //@ produce_call_below_perm_();
  //@ open spinlock_classic(_, _, _);
  //@ int acquireCredits = spinlock->acquireCredits;
  //@ box signalsBox = spinlock->signalsBox;
  {
    /*@
    predicate pre_() =
      is_spinlock_classic_acquire_ghost_op(ghop, inv, pre, post) &*& pre() &*&
      [f]spinlock->acquireCredits |-> acquireCredits &*&
      [f]spinlock->signalsBox |-> signalsBox &*&
      obs(p, obs) &*&
      exists<bool>(?started) &*&
      !started ?
        call_below_perm_(currentThread, spinlock_classic_acquire)
      :
        has_at(_, signalsBox, ?k, ?signal) &*&
        wait_perm(p, signal, level, spinlock_acquire) &*&
        call_below_perms(acquireCredits - k, p, spinlock_classic_acquire);
    predicate post_() =
      post() &*&
      [f]spinlock->acquireCredits |-> acquireCredits &*&
      [f]spinlock->signalsBox |-> signalsBox &*& [1/2]spinlock->signals |-> ?signals &*& 0 < length(signals) &*&
      obs(p, cons(pair(nth(length(signals) - 1, signals), level), obs));
    @*/
    /*@
    produce_lemma_function_pointer_chunk spinlock_acquire_ghost_op(spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox), pre_, post_, currentThread)() {
      open spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)(?locked);
      open pre_();
      assert growing_list(signalsBox, ?signals);
      if (locked) {
        open exists<bool>(?started);
        if (!started) {
          int k = length(signals) - 1;
          void *s = nth(k, signals);
          pathize_call_below_perm__multi(acquireCredits + 1);
          open call_below_perms(_, _, _);
          produce_func_lt(spinlock_acquire);
          create_wait_perm(s, level, spinlock_acquire);
          is_ancestor_of_refl(p);
          wait(s);
          consuming_box_predicate growing_list(signalsBox, _)
          perform_action noop() {}
          producing_box_predicate growing_list(signals)
          producing_fresh_handle_predicate has_at(k, s);
          call_below_perms_weaken(acquireCredits - k);
        } else {
          assert has_at(?handleId, signalsBox, ?k, ?s);
          consuming_box_predicate growing_list(signalsBox, signals)
          consuming_handle_predicate has_at(handleId, k, s)
          perform_action noop() {}
          producing_box_predicate growing_list(signals)
          producing_handle_predicate has_at(handleId, length(signals) - 1, nth(length(signals) - 1, signals));
          if (k == length(signals) - 1) {
          } else {
            leak wait_perm(_, _, _, _);
            k = length(signals) - 1;
            s = nth(k, signals);
            open call_below_perms(_, _, _);
            call_below_perms_weaken(acquireCredits - k);
            produce_func_lt(spinlock_acquire);
            create_wait_perm(s, level, spinlock_acquire);
          }
          is_ancestor_of_refl(p);
          wait(s);
        }
        close spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)(locked);
        close exists<bool>(true);
        close pre_();
      } else {
        void *s = create_signal();
        init_signal(s, level);
        consuming_box_predicate growing_list(signalsBox, signals)
        perform_action add(s) {}
        producing_box_predicate growing_list(append(signals, {s}));
        spinlock->signals = append(signals, {s});
        produce_func_lt(spinlock_acquire);
        assert atomic_spaces(?spaces);
        if (!forall(spaces, (space_name_lt)(spinlock_classic_acquire))) {
            pair<void *, predicate()> space = not_forall(spaces, (space_name_lt)(spinlock_classic_acquire));
            forall_elim(spaces, (space_name_lt)(spinlock_acquire), space);
            assert false;
        }
        ghop();
        leak is_spinlock_classic_acquire_ghost_op(_, _, _, _);
        nth_append_r(signals, {s}, 0);
        assert s == nth(length(append(signals, {s})) - 1, append(signals, {s}));
        close spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)(true);
        close post_();
        open exists<bool>(?started);
        if (!started) {
          leak call_below_perm_(_, _);
        } else {
          leak has_at(_, _, _, _);
          leak call_below_perms(_, _, _);
          leak wait_perm(_, _, _, _);
        }
      }
    };
    @*/
    //@ close exists(false);
    //@ close pre_();
    spinlock_acquire(spinlock->spinlock);
    //@ open post_();
    //@ assert obs(p, cons(?ob, obs));
    //@ close spinlock_classic_held(spinlock, f, inv, ob);
  }
}

/*@

typedef lemma void spinlock_classic_release_ghost_op(predicate(int, bool) inv, predicate() pre, predicate() post)();
    requires inv(?acquireCredits, true) &*& pre();
    ensures inv(acquireCredits, false) &*& post();

@*/

void spinlock_classic_release(spinlock_classic_t spinlock)
//@ requires obs(?p, cons(?ob, ?obs)) &*& spinlock_classic_held(spinlock, ?f, ?inv, ob) &*& is_spinlock_classic_release_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures obs(p, obs) &*& [f]spinlock_classic(spinlock, level_of(ob), inv) &*& post();
{
  //@ open spinlock_classic_held(spinlock, f, inv, pair(?s, ?level));
  //@ int acquireCredits = spinlock->acquireCredits;
  //@ box signalsBox = spinlock->signalsBox;
  //@ list<void *> signals = spinlock->signals;
  {
    /*@
    predicate pre_() = obs(p, cons(ob, obs)) &*& is_spinlock_classic_release_ghost_op(ghop, inv, pre, post) &*& pre() &*& [1/2]spinlock->signals |-> signals;
    predicate post_() = obs(p, obs) &*& post();
    @*/
    /*@
    produce_lemma_function_pointer_chunk spinlock_release_ghost_op(spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox), pre_, post_)() {
      open spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)(_);
      open pre_();
      ghop();
      leak is_spinlock_classic_release_ghost_op(_, _, _, _);
      set_signal(s);
      leak signal(_, _, true);
      close spinlock_classic_inv(spinlock, level, inv, acquireCredits, signalsBox)(false);
      close post_();
    };
    @*/
    //@ close pre_();
    spinlock_release(spinlock->spinlock);
    //@ open post_();
  }
}
