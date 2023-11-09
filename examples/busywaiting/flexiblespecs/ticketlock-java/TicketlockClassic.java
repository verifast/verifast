/*@

inductive wrapper<t> = wrapper(t);

predicate_ctor TicketlockClassic_inv(TicketlockClassic l)() =
  [_]l.inv_ |-> wrapper(?inv) &*&
  [_]l.lock |-> ?lock &*& lock.state(?owner, ?held) &*&
  held ? true : inv();

fixpoint list<int> LOCK_NS() { return {0}; }
fixpoint list<int> SPACE_NS() { return {1}; }

@*/

final class TicketlockClassic {
  //@ wrapper<predicate()> inv_;
  private Ticketlock lock;

  /*@
  predicate valid(predicate() inv) =
    [_]this.inv_ |-> wrapper(inv) &*&
    [_]this.lock |-> ?lock &*& [_]lock.valid(LOCK_NS) &*&
    [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this));
  @*/

  //@ predicate held() = [_]this.lock |-> ?lock &*& lock.held(_);

  public TicketlockClassic()
  //@ requires exists<predicate()>(?inv) &*& inv();
  //@ ensures [_]valid(inv);
  {
    //@ close exists(LOCK_NS);
    lock = new Ticketlock();
    //@ this.inv_ = wrapper(inv);
    //@ leak this.inv_ |-> _ &*& this.lock |-> _;
    //@ close TicketlockClassic_inv(this)();
    //@ create_atomic_space_(SPACE_NS, TicketlockClassic_inv(this));
  }

  public void acquire()
  //@ requires [_]valid(?inv);
  //@ ensures held() &*& inv();
  {
    Ticketlock lock = this.lock;
    {
      /*@
      predicate pre() =
        [_]this.lock |-> lock &*&
        [_]this.inv_ |-> wrapper(inv) &*&
        [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this));
      predicate post(int result) = inv();
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(lock, LOCK_NS, pre, post)(op) {
        open pre();
        assert atomic_spaces(?spaces);
        if (mem(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces)) {
          mem_map(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)(LOCK_NS), SPACE_NS);
          assert false;
        }
        open_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        open TicketlockClassic_inv(this)();
        assert lock.state(?owner, ?held);
        op();
        close TicketlockClassic_inv(this)();
        close_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        close post(owner);
      };
      @*/
      //@ close pre();
      lock.acquire();
      //@ open post(_);
    }
  }

  public void release()
  //@ requires [_]valid(?inv) &*& held() &*& inv();
  //@ ensures true;
  {
    Ticketlock lock = this.lock;
    //@ open held();
    //@ assert lock.held(?ticket);
    {
      /*@
      predicate pre() =
        [_]this.lock |-> lock &*&
        [_]this.inv_ |-> wrapper(inv) &*&
        [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this)) &*& inv();
      predicate post() = true;
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(lock, LOCK_NS, ticket, pre, post)(op) {
        open pre();
        assert atomic_spaces(?spaces);
        if (mem(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces)) {
          mem_map(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)(LOCK_NS), SPACE_NS);
          assert false;
        }
        open_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        open TicketlockClassic_inv(this)();
        op();
        close TicketlockClassic_inv(this)();
        close_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        close post();
      };
      @*/
      //@ close pre();
      lock.release();
      //@ open post();
    }
  }
}
