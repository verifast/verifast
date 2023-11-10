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
  //@ requires true;
  //@ ensures true;
  {
    Flag flag = new Flag();
    //@ close Flag_valid(flag)();
    //@ close exists(pair(L, Flag_valid(flag)));
    TicketlockClassic lock = new TicketlockClassic();
    Flipper flipper = new Flipper();
    flipper.flag = flag;
    flipper.lock = lock;
    //@ leak flipper.flag |-> _ &*& flipper.lock |-> _;
    new Thread(flipper).start();
    new Thread(flipper).start();
  }
}
