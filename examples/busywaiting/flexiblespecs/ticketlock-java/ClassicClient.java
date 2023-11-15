// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

final class Flag {
  int value;
}

//@ fixpoint level L() { return level(ClassicClient.class, {TicketlockClassic_level_nb_dims}); }

//@ predicate_ctor Flag_valid(Flag flag)() = flag.value |-> ?v &*& v == 0 || v == 1;

final class Flipper implements Runnable {
  Flag flag;
  TicketlockClassic lock;
  //@ predicate valid() = [_]flag |-> ?flag_ &*& [_]lock |-> ?lock_ &*& [_]lock_.valid(L, Flag_valid(flag_));
  public void run()
  //@ requires obs(currentThread, ?p, {}) &*& valid();
  //@ ensures obs(currentThread, p, {});
  //@ terminates;
  {
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
  //@ ensures obs(currentThread, {}, {});
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
    new Thread(flipper).start();
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Flipper.class);
    new Thread(flipper).start();
  }
}
