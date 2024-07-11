// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

final class Flag {
  int value;
}

//@ fixpoint level L() { return level(ClassicClient.class, {TicketlockClassic_level_nb_dims}); }

//@ predicate_ctor Flag_valid(Flag flag)() = flag.value |-> ?v &*& v == 0 || v == 1;

/*@

predicate_family_instance Runnable_pre(Flipper.class)(Flipper flipper, int threadId) =
    obs(threadId, _, {}) &*&
    [_]flipper.flag |-> ?flag_ &*& [_]flipper.lock |-> ?lock_ &*& [_]lock_.valid(L, Flag_valid(flag_));

@*/

final class Flipper implements Runnable {
  Flag flag;
  TicketlockClassic lock;
  public void run()
  //@ requires Runnable_pre(Flipper.class)(this, currentThread);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ open Runnable_pre(Flipper.class)(this, currentThread);
    lock.acquire();
    //@ open Flag_valid(flag)();
    flag.value = 1 - flag.value;
    //@ close Flag_valid(flag)();
    lock.release();
  }
}

final class ClassicClient {
  public static void main(String[] args)
  //@ requires obs(currentThread, {}, {});
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    Flag flag = new Flag();
    //@ close Flag_valid(flag)();
    //@ close exists(pair(L, Flag_valid(flag)));
    TicketlockClassic lock = new TicketlockClassic();
    Flipper flipper = new Flipper();
    flipper.flag = flag;
    flipper.lock = lock;
    //@ leak flipper.flag |-> _ &*& flipper.lock |-> _;
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Flipper.class);
    {
      /*@
      predicate pre() =
        [_]flipper.flag |-> ?flag_ &*& [_]flipper.lock |-> ?lock_ &*& [_]lock_.valid(L, Flag_valid(flag_));
      predicate post() =
        obs(currentThread, {Forker}, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {}, {}, {}, flipper, pre, post)(forkeeId) {
        open pre();
        close post();
        close Runnable_pre(Flipper.class)(flipper, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(flipper).start();
      //@ open post();
    }
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Flipper.class);
    {
      /*@
      predicate pre() =
        [_]flipper.flag |-> ?flag_ &*& [_]flipper.lock |-> ?lock_ &*& [_]lock_.valid(L, Flag_valid(flag_));
      predicate post() =
        obs(currentThread, {Forker, Forker}, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {Forker}, {}, {}, flipper, pre, post)(forkeeId) {
        open pre();
        close post();
        close Runnable_pre(Flipper.class)(flipper, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(flipper).start();
      //@ open post();
    }
  }
}
