// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

inductive wrapper<t> = wrapper(t);

predicate_ctor TicketlockClassic_inv(TicketlockClassic l)() =
  [_]l.inv_ |-> wrapper(?inv) &*&
  [_]l.lock |-> ?lock &*& lock.state(?owner, ?held) &*&
  [_]l.level |-> ?level &*&
  [_]l.signalsId |-> ?signalsId &*& growing_list<void *>(signalsId, ?signals) &*& length(signals) == owner + (held ? 1 : 0) &*&
  held ? signal(nth(owner, signals), level, false) : inv();

fixpoint list<int> LOCK_NS() { return {0}; }
fixpoint list<int> SPACE_NS() { return {1}; }

predicate TicketlockClassic_held(TicketlockClassic l, pair<void *, level> ob) =
    [_]l.lock |-> ?lock &*& lock.held(?ticket) &*&
    [_]l.level |-> ?level &*&
    [_]l.signalsId |-> ?signalsId &*& has_at<void *>(_, signalsId, ticket, ?signal) &*& ob == pair(signal, level);

@*/

final class TicketlockClassic {
  //@ level level;
  //@ wrapper<predicate()> inv_;
  private Ticketlock lock;
  //@ box signalsId;

  /*@
  predicate valid(level level, predicate() inv) =
    [_]this.level |-> level &*& TicketlockClassic_level_nb_dims <= level_subspace_nb_dims(level) &*&
    [_]this.inv_ |-> wrapper(inv) &*&
    [_]this.signalsId |-> _ &*&
    [_]this.lock |-> ?lock &*& [_]lock.valid(LOCK_NS, level) &*&
    [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this));
  @*/
  
  public TicketlockClassic()
  //@ requires exists<pair<level, predicate()> >(pair(?level, ?inv)) &*& inv() &*& TicketlockClassic_level_nb_dims <= level_subspace_nb_dims(level);
  //@ ensures [_]valid(level, inv);
  //@ terminates;
  {
    //@ assert level == level(_, cons(_, _));
    //@ close exists(pair(LOCK_NS, level));
    lock = new Ticketlock();
    //@ this.level = level;
    //@ this.inv_ = wrapper(inv);
    //@ box signalsId = create_growing_list<void *>();
    //@ this.signalsId = signalsId;
    //@ leak this.level |-> _ &*& this.inv_ |-> _ &*& this.lock |-> _ &*& this.signalsId |-> _;
    //@ close TicketlockClassic_inv(this)();
    //@ create_atomic_space_(SPACE_NS, TicketlockClassic_inv(this));
  }

  public void acquire()
  //@ requires obs(currentThread, ?p, ?obs) &*& [_]valid(?level, ?inv) &*& forall(map(snd, obs), (level_subspace_lt)(level)) == true;
  //@ ensures obs(currentThread, p, cons(?ob, obs)) &*& TicketlockClassic_held(this, ob) &*& level_le(level, level_of(ob)) == true &*& inv();
  //@ terminates;
  {
    Ticketlock lock = this.lock;
    //@ box signalsId = this.signalsId;
    {
      /*@
      predicate waitInv(int oldOwner) =
        [_]this.lock |-> lock &*&
        [_]this.level |-> level &*&
        [_]this.inv_ |-> wrapper(inv) &*&
        [_]this.signalsId |-> signalsId &*&
        [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this)) &*&
        oldOwner == -1 ?
          true
        :
          exists(?signalHandle) &*&
          has_at(signalHandle, signalsId, oldOwner, ?signal) &*& wait_perm(p, signal, level, Ticketlock_targetClass);
      predicate post(int result) =
        has_at(_, signalsId, result, ?signal) &*&
        obs(currentThread, p, cons(pair(signal, level), obs)) &*&
        inv();
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_wait_ghost_op(p, lock, LOCK_NS, level, 1, waitInv, currentThread)(owner, newRound, op) {
        open waitInv(?oldOwner);
        handle signalHandle;
        if (oldOwner != -1) {
          open exists(?signalHandle_);
          signalHandle = signalHandle_;
        }
        assert atomic_spaces(?spaces);
        if (mem(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces)) {
          mem_map(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)(LOCK_NS), SPACE_NS);
          assert false;
        }
        open_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        open TicketlockClassic_inv(this)();
        op();
        //assert is_Ticketlock_wait_op(op, lock, owner, ?P);
        assert growing_list(signalsId, ?signals);
        void *signal = nth(owner, signals);
        if (newRound) {
          open cp_lex(?t, ?c, {1});
          call_below_perm_lex_weaken({0});
          create_wait_perm(signal, level, c);
          signalHandle = create_has_at(signalsId, owner);
        } else {
          match_has_at(signalsId);
        }
        is_ancestor_of_refl(p);
        wait(signal);
        close exists(signalHandle);
        close waitInv(owner);
        close TicketlockClassic_inv(this)();
        close_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(p, obs, lock, LOCK_NS, waitInv, post, currentThread)(owner, op) {
        open waitInv(_);
        assert atomic_spaces(?spaces);
        if (mem(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces)) {
          mem_map(pair(SPACE_NS, TicketlockClassic_inv(this)), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)(LOCK_NS), SPACE_NS);
          assert false;
        }
        open_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        open TicketlockClassic_inv(this)();
        op();
        void *signal = create_signal();
        init_signal(signal, level);
        assert growing_list(signalsId, ?signals);
        growing_list_add(signalsId, signal);
        nth_append_r(signals, {signal}, 0);
        create_has_at(signalsId, owner);
        close TicketlockClassic_inv(this)();
        close_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        close post(owner);
      };
      @*/
      //@ close waitInv(-1);
      //@ produce_call_below_perm_();
      //@ call_below_perm__weaken(Ticketlock.class);
      lock.acquire();
      //@ open post(?ticket);
      //@ assert has_at(_, signalsId, ticket, ?signal);
      //@ close TicketlockClassic_held(this, pair(signal, level));
    }
  }

  public void release()
  /*@
  requires
    obs(currentThread, ?p, ?obs) &*& [_]valid(?level, ?inv) &*& TicketlockClassic_held(this, ?ob) &*& inv() &*& mem(ob, obs) == true &*&
    forall(map(snd, remove(ob, obs)), (level_subspace_lt)(level)) == true;
  @*/
  //@ ensures obs(currentThread, p, remove(ob, obs));
  //@ terminates;
  {
    Ticketlock lock = this.lock;
    //@ open TicketlockClassic_held(this, pair(?signal, _));
    //@ assert lock.held(?ticket);
    {
      /*@
      predicate pre() =
        obs(currentThread, p, obs) &*&
        [_]this.lock |-> lock &*&
        [_]this.level |-> level &*&
        [_]this.inv_ |-> wrapper(inv) &*&
        [_]this.signalsId |-> ?signalsId &*&
        [_]atomic_space_(SPACE_NS, TicketlockClassic_inv(this)) &*& inv() &*&
        has_at(_, signalsId, ticket, signal);
      predicate post(list<pathcomp> p_, list<pair<void *, level> > obs_) = p_ == p &*& obs_ == remove(ob, obs);
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(lock, LOCK_NS, level, ticket, pre, post, currentThread)(op) {
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
        match_has_at(signalsId);
        set_signal(signal);
        close TicketlockClassic_inv(this)();
        close_atomic_space(SPACE_NS, TicketlockClassic_inv(this));
        close post(p, remove(ob, obs));
      };
      @*/
      //@ close pre();
      lock.release();
      //@ open post(_, _);
    }
  }
}
