// tab_size:2

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

public final class Spinlock {

  //@ list<int> ns;
  //@ level level;
  private AtomicLong lk;

  //@ predicate valid(list<int> ns, level level) = this.ns |-> ns &*& this.level |-> level &*& [_]lk |-> ?_lk &*& _lk != null &*& 0 <= level_subspace_nb_dims(level);

  //@ predicate held() = [_]lk |-> ?_lk &*& [1/2]_lk.state(true);
  
  //@ predicate state(boolean held) = [_]lk |-> ?_lk &*& [1/2]_lk.state(?value) &*& value == 0 ? [1/2]_lk.state(false) &*& held == false : value == 1 &*& held == true;

  public Spinlock()
  //@ requires exists<pair<list<int>, level> >(pair(?ns, ?level)) &*& Spinlock_level_nb_dims <= level_subspace_nb_dims(level);
  //@ ensures [_]valid(ns, level) &*& state(false);
  //@ terminates;
  {
    //@ this.ns = ns;
    //@ this.level = level;
    lk = new AtomicLong();
    //@ close state(false);
  }

  public void acquire()
  /*@
  requires
    [_]valid(?ns, ?level) &*&
    obs(currentThread, ?p, ?obs) &*& forall(map(snd, obs), (level_subspace_lt)(level)) == true &*&
    is_Spinlock_sep(?sep, this, ns, ?waitInv, ?R) &*&
    is_Spinlock_wait_ghost_op(?wop, this, R, currentThread, p, level, waitInv) &*&
    is_Spinlock_acquire_ghost_op(?aop, this, R, p, obs, ?post, currentThread) &*&
    waitInv();
  @*/
  //@ ensures held() &*& post();
  //@ terminates;
  {
    //@ AtomicLong _lk = lk;
    for (;;)
    /*@
    invariant
      [_]lk |-> _lk &*&
      obs(currentThread, p, obs) &*&
      is_Spinlock_sep(sep, this, ns, waitInv, R) &*&
      is_Spinlock_wait_ghost_op(wop, this, R, currentThread, p, level, waitInv) &*&
      is_Spinlock_acquire_ghost_op(aop, this, R, p, obs, post, currentThread) &*&
      waitInv();
    @*/
    {
      boolean success;
      {
        /*@
        predicate pre_() =
          [_]lk |-> _lk &*&
          obs(currentThread, p, obs) &*&
          is_Spinlock_sep(sep, this, ns, waitInv, R) &*&
          is_Spinlock_wait_ghost_op(wop, this, R, currentThread, p, level, waitInv) &*&
          is_Spinlock_acquire_ghost_op(aop, this, R, p, obs, post, currentThread) &*&
          waitInv();
        predicate post_(boolean success_) =
          is_Spinlock_sep(sep, this, ns, waitInv, R) &*&
          is_Spinlock_wait_ghost_op(wop, this, R, currentThread, p, level, waitInv) &*&
          is_Spinlock_acquire_ghost_op(aop, this, R, p, obs, post, currentThread) &*&
          success_ ?
            post() &*& [1/2]_lk.state(true)
          :
            obs(currentThread, p, obs) &*&
            waitInv() &*&
            call_perm_(currentThread, Spinlock.class);
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_compareAndSet_ghost_op(_lk, 0, 1, pre_, post_)(op) {
          open pre_();
          sep();
          open state(?held);
          assert [_]_lk.state(?value);
          op();
          if (held) {
            if (!forall(map(snd, obs), (level_lt)(level))) {
              level badLevel = not_forall(map(snd, obs), (level_lt)(level));
              forall_elim(map(snd, obs), (level_subspace_lt)(level), badLevel);
              level_subspace_lt_level_lt(level, {}, badLevel);
              assert false;
            }
            wop();
            close post_(false);
          } else {
            aop();
            close post_(true);
          }
        };
        @*/
        //@ close pre_();
        success = lk.compareAndSet(0, 1);
        //@ open post_(success);
      }
      if (success)
        break;
    }
    //@ close held();
  }

  public void release()
  /*@
  requires
    [_]valid(?ns, ?level) &*&
    held() &*&
    is_Spinlock_sep(?sep, this, ns, ?pre, ?R) &*&
    is_Spinlock_release_ghost_op(?ghop, this, R, ?post, currentThread) &*& pre();
  @*/
  //@ ensures post(?p, ?obs) &*& obs(currentThread, p, obs);
  //@ terminates;
  {
    //@ AtomicLong _lk = lk;
    {
      /*@
      predicate pre_() =
        [_]lk |-> _lk &*& [1/2]_lk.state(true) &*&
        is_Spinlock_sep(sep, this, ns, pre, R) &*&
        is_Spinlock_release_ghost_op(ghop, this, R, post, currentThread) &*&
        pre();
      predicate post_() =
        post(?p, ?obs) &*& obs(currentThread, p, obs);
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_set_ghost_op(_lk, 0, pre_, post_)(op) {
        open pre_();
        sep();
        open state(?held);
        op();
        ghop();
        close post_();
      };
      @*/
      //@ close pre_();
      lk.set(0);
      //@ open post_();
    }
  }

}
