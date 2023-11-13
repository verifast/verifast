// tab_size:2

/*@

fixpoint int Ticketlock_level_nb_dims() { return 1; }

fixpoint Class Ticketlock_targetClass() { return TicketlockStrong.class; }

typedef lemma void Ticketlock_wait_op(Ticketlock l, int owner_, predicate() P)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, held) &*& owner == owner_ &*& held &*& P();

typedef lemma void Ticketlock_wait_ghost_op(list<pathcomp> p, Ticketlock l, list<int> ns, level level, int nbDegrees, predicate(int oldOwner) waitInv, int callerThread)(int owner, boolean newRound, Ticketlock_wait_op *op);
  requires
    obs(callerThread, p, ?obs) &*& forall(map(snd, obs), (level_lt)(level)) == true &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_wait_op(op, l, owner, ?P) &*& P() &*&
    0 <= owner &*&
    waitInv(?oldOwner) &*&
    newRound ?
      cp_lex(p, Ticketlock_targetClass, {nbDegrees})
    :
      owner == oldOwner;
  ensures
    obs(callerThread, p, obs) &*&
    atomic_spaces(spaces) &*&
    is_Ticketlock_wait_op(op, l, owner, P) &*& P() &*&
    call_perm_(callerThread, Ticketlock_targetClass) &*& waitInv(owner);

typedef lemma void Ticketlock_acquire_op(Ticketlock l, int owner_, predicate() P, predicate() Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, true) &*& owner == owner_ &*& !held &*& Q();

typedef lemma void Ticketlock_acquire_ghost_op(list<pathcomp> p, list<pair<void *, level> > obs, Ticketlock l, list<int> ns, predicate(int oldOwner) waitInv, predicate(int) post, int callerThread)(int owner, Ticketlock_acquire_op *op);
  requires
    obs(callerThread, p, obs) &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_acquire_op(op, l, owner, ?P, ?Q) &*& P() &*& 0 <= owner &*& waitInv(_);
  ensures
    atomic_spaces(spaces) &*&
    is_Ticketlock_acquire_op(op, l, owner, P, Q) &*& Q() &*&
    post(owner);

typedef lemma void Ticketlock_release_op(Ticketlock l, long ticket, predicate() P, predicate() Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(ticket + 1, false) &*& owner == ticket &*& held &*& Q();

typedef lemma void Ticketlock_release_ghost_op(Ticketlock l, list<int> ns, long ticket, predicate() pre, predicate() post)(Ticketlock_release_op *op);
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_release_op(op, l, ticket, ?P, ?Q) &*& P() &*& pre();
  ensures
    atomic_spaces(spaces) &*&
    is_Ticketlock_release_op(op, l, ticket, P, Q) &*& Q() &*& post();

predicate Ticketlock_not_alone(Ticketlock lock, int owner) = [_]lock.lock |-> ?lock_ &*& TicketlockStrong_not_alone(lock_, owner);

lemma void Ticketlock_not_alone_elim(Ticketlock this)
  requires
    [_]this.valid(?ns, ?level) &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (not_is_prefix_of)(ns)) == true &*&
    Ticketlock_not_alone(this, ?ticket) &*&
    this.state(?owner, ?held);
  ensures
    atomic_spaces(spaces) &*&
    Ticketlock_not_alone(this, ticket) &*&
    this.state(owner, held) &*& owner != ticket || held;
{
  open this.valid(ns, level);
  open this.state(owner, held);
  open Ticketlock_not_alone(this, ticket);
  TicketlockStrong_not_alone_elim(this.lock);
  close Ticketlock_not_alone(this, ticket);
}

@*/

public final class Ticketlock {
  TicketlockStrong lock;
  //@ level level;

  /*@
  predicate valid(list<int> ns, level level) =
    [_]this.level |-> level &*& Ticketlock_level_nb_dims <= level_subspace_nb_dims(level) &*&
    [_]lock |-> ?lock &*& [_]lock.valid(ns);
  @*/
  
  //@ predicate held(long ticket) = [_]lock |-> ?lock &*& lock.held(ticket);
  
  //@ predicate state(int owner, boolean held) = [_]lock |-> ?lock &*& lock.state(owner, held);

  public Ticketlock()
  //@ requires exists<pair<list<int>, level> >(pair(?ns, ?level)) &*& Ticketlock_level_nb_dims <= level_subspace_nb_dims(level);
  //@ ensures [_]valid(ns, level) &*& state(0, false);
  //@ terminates;
  {
    //@ open exists(_);
    //@ close exists(ns);
    //@ this.level = level;
    lock = new TicketlockStrong();
    //@ leak this.lock |-> _ &*& this.level |-> _;
    //@ close state(0, false);
  }

  public void acquire()
  /*@
  requires
    [_]valid(?ns, ?level) &*&
    obs(currentThread, ?p, ?obs) &*& forall(map(snd, obs), (level_subspace_lt)(level)) == true &*&
    is_Ticketlock_wait_ghost_op(?wop, p, this, ns, level, ?nbDegrees, ?waitInv, currentThread) &*&
    is_Ticketlock_acquire_ghost_op(?aop, p, obs, this, ns, waitInv, ?post, currentThread) &*&
    waitInv(-1) &*& call_below_perm_(currentThread, Ticketlock.class);
  @*/
  //@ ensures held(?ticket) &*& post(ticket);
  //@ terminates;
  {
    TicketlockStrong lock = this.lock;
    {
      /*@
      predicate waitInv_(int oldOwner, int oldM) =
        [_]this.lock |-> lock &*&
        obs(currentThread, p, obs) &*&
        waitInv(oldOwner) &*&
        is_Ticketlock_wait_ghost_op(wop, p, this, ns, level, nbDegrees, waitInv, currentThread) &*&
        is_Ticketlock_acquire_ghost_op(aop, p, obs, this, ns, waitInv, post, currentThread) &*&
        oldOwner == -1 ?
          call_below_perm_(currentThread, Ticketlock.class)
        :
          call_below_perms_lex(oldM, p, Ticketlock.class, {nbDegrees});
      @*/
      /*@
      produce_lemma_function_pointer_chunk TicketlockStrong_wait_ghost_op(lock, ns, waitInv_, currentThread)(owner, M, op) {
        assert is_TicketlockStrong_wait_op(op, lock, owner, ?P);
        open waitInv_(?oldOwner, ?oldM);
        {
          predicate P_() = [_]this.lock |-> lock &*& is_TicketlockStrong_wait_op(op, lock, owner, P) &*& P();
          produce_lemma_function_pointer_chunk Ticketlock_wait_op(this, owner, P_)() {
            open P_();
            open this.state(_, _);
            op();
            close this.state(owner, true);
            close P_();
          } {
            if (!forall(map(snd, obs), (level_lt)(level))) {
                level badLevel = not_forall(map(snd, obs), (level_lt)(level));
                forall_elim(map(snd, obs), (level_subspace_lt)(level), badLevel);
                level_subspace_lt_level_lt(level, {}, badLevel);
                assert false;
            }
            close P_();
            assert is_Ticketlock_wait_op(?op_, _, _, _);
            if (oldOwner == -1 || M < oldM) {
              if (oldOwner == -1) {
                pathize_call_below_perm__lex_multi(M + 1, {nbDegrees});
              } else {
                call_below_perms_lex_weaken(M + 1);
              }
              open call_below_perms_lex(M + 1, _, _, _);
              close cp_lex(p, TicketlockStrong.class, {nbDegrees});
            }
            wop(owner, (oldOwner == -1 || M < oldM), op_);
            open P_();
          }
        }
        close waitInv_(owner, M);
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk TicketlockStrong_acquire_ghost_op(lock, ns, waitInv_, post)(owner, op) {
        assert is_TicketlockStrong_acquire_op(op, lock, owner, ?P, ?Q);
        open waitInv_(_, _);
        {
          predicate P_() = [_]this.lock |-> lock &*& is_TicketlockStrong_acquire_op(op, lock, owner, P, Q) &*& P();
          predicate Q_() = is_TicketlockStrong_acquire_op(op, lock, owner, P, Q) &*& Q();
          produce_lemma_function_pointer_chunk Ticketlock_acquire_op(this, owner, P_, Q_)() {
            open P_();
            open this.state(_, _);
            op();
            close this.state(owner, true);
            close Q_();
          } {
            close P_();
            assert is_Ticketlock_acquire_op(?op_, _, _, _, _);
            aop(owner, op_);
            open Q_();
          }
        }
      };
      @*/
      //@ close waitInv_(-1, 0);
      lock.acquire();
    }
  }

  public boolean alone()
  //@ requires [_]valid(?ns, ?level) &*& held(?ticket);
  //@ ensures held(ticket) &*& result ? true : Ticketlock_not_alone(this, ticket);
  {
    //@ open valid(ns, level);
    //@ open held(ticket);
    boolean result = lock.alone();
    //@ if (!result) close Ticketlock_not_alone(this, ticket);
    return result;
  }
  
  public void release()
  //@ requires [_]valid(?ns, ?level) &*& held(?ticket) &*& is_Ticketlock_release_ghost_op(?ghop, this, ns, ticket, ?pre, ?post) &*& pre();
  //@ ensures post();
  //@ terminates;
  {
    TicketlockStrong lock = this.lock;
    //@ open valid(ns, level);
    //@ open held(ticket);
    {
      /*@
      predicate pre_() = [_]this.lock |-> lock &*& is_Ticketlock_release_ghost_op(ghop, this, ns, ticket, pre, post) &*& pre();
      @*/
      /*@
      produce_lemma_function_pointer_chunk TicketlockStrong_release_ghost_op(lock, ns, ticket, pre_, post)(op) {
        open pre_();
        assert is_TicketlockStrong_release_op(op, lock, ticket, ?P, ?Q);
        {
          predicate P_() = [_]this.lock |-> lock &*& is_TicketlockStrong_release_op(op, lock, ticket, P, Q) &*& P();
          predicate Q_() = [_]this.lock |-> lock &*& is_TicketlockStrong_release_op(op, lock, ticket, P, Q) &*& Q();
          produce_lemma_function_pointer_chunk Ticketlock_release_op(this, ticket, P_, Q_)() {
            open P_();
            open this.state(_, _);
            op();
            close this.state(ticket + 1, false);
            close Q_();
          } {
            close P_();
            assert is_Ticketlock_release_op(?op_, _, _, _, _);
            ghop(op_);
            open Q_();
          }
        }
      };
      @*/
      //@ close pre_();
      lock.release();
    }
  }
}
