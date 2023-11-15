// tab_size:2

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

inductive thread_info = thread_info(predicate(int, int) waitInv, predicate(int) post, boolean grabbed);

predicate waiting_threads(TicketlockStrong lock, list<int> ns, list<int> cellIds, int index, int owner) =
    switch (cellIds) {
        case nil: return true;
        case cons(cellId, cellIds0): return
            [1/2]ghost_cell(cellId, thread_info(?waitInv, ?post, false)) &*&
            is_TicketlockStrong_acquire_ghost_op(_, lock, ns, waitInv, post) &*&
            waitInv(?oldOwner, ?oldM) &*& oldOwner == -1 || index - owner < oldM || index - owner == oldM && owner == oldOwner &*&
            waiting_threads(lock, ns, cellIds0, index + 1, owner);
    };

predicate grabbed_cell(int cellId) = ghost_cell(cellId, thread_info(_, _, true));

predicate_ctor TicketlockStrong_inv(TicketlockStrong l)() =
  [_]l.ns |-> ?ns &*&
  [_]l.owner |-> ?owner_ &*& [1/2]owner_.state(?owner) &*& 0 <= owner &*&
  [_]l.next |-> ?next_ &*& next_.state(?next) &*&
  [1/4]l.owner_ |-> owner &*& owner <= next &*&
  [1/4]l.held |-> ?held &*&
  [_]l.growingListId |-> ?growingListId &*& growing_list<int>(growingListId, ?cellIds) &*& length(cellIds) == next &*&
  foreach(take(owner, cellIds), grabbed_cell) &*&
  owner < next ?
    waiting_threads(l, ns, drop(owner + 1, cellIds), owner + 1, owner) &*&
    [1/2]ghost_cell(nth(owner, cellIds), thread_info(?waitInv, ?post, ?grabbed)) &*&
    (grabbed ? [1/2]ghost_cell<thread_info>(nth(owner, cellIds), _) : post(owner) &*& [1/2]owner_.state(owner) &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> true) &*&
    held
  :
    !held &*& [1/2]owner_.state(owner) &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> false;

predicate TicketlockStrong_not_alone(TicketlockStrong lock, int owner) =
  [_]lock.growingListId |-> ?growingListId &*& has_at<int>(_, growingListId, owner + 1, _);

lemma void TicketlockStrong_not_alone_elim(TicketlockStrong this)
  requires
    [_]this.valid(?ns) &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (not_is_prefix_of)(ns)) == true &*&
    TicketlockStrong_not_alone(this, ?ticket) &*&
    this.state(?owner, ?held);
  ensures
    atomic_spaces(spaces) &*&
    TicketlockStrong_not_alone(this, ticket) &*&
    this.state(owner, held) &*& owner != ticket + 1 || held;
{
  open this.valid(ns);
  if (mem(pair(ns, TicketlockStrong_inv(this)), spaces)) {
    mem_map(pair(ns, TicketlockStrong_inv(this)), spaces, fst);
    forall_elim(map(fst, spaces), (not_is_prefix_of)(ns), ns);
    assert false;
  }
  open_atomic_space(ns, TicketlockStrong_inv(this));
  open TicketlockStrong_inv(this)();
  
  open this.state(owner, held);
  open TicketlockStrong_not_alone(this, ticket);
  match_has_at(growingListId);
  close TicketlockStrong_not_alone(this, ticket);
  close this.state(owner, held);
  
  close TicketlockStrong_inv(this)();
  close_atomic_space(ns, TicketlockStrong_inv(this));
}

@*/

public final class TicketlockStrong {
  private AtomicLong owner;
  private AtomicLong next;
  //@ long owner_;
  //@ boolean held;
  //@ box growingListId;
  //@ list<int> ns;

  /*@
  predicate valid(list<int> ns) =
    [_]this.ns |-> ns &*&
    [_]this.owner |-> ?owner &*& owner != null &*&
    [_]this.next |-> ?next &*& next != null &*&
    [_]this.growingListId |-> _ &*&
    atomic_space_(ns, TicketlockStrong_inv(this));
  @*/
  
  /*@
  predicate held(long ticket) =
    [_]owner |-> ?owner &*&
    [1/2]owner.state(ticket) &*&
    [1/4]owner_ |-> ticket &*&
    [1/4]held |-> true &*&
    [_]growingListId |-> ?growingListId;
  @*/
  
  /*@
  predicate state(int owner, boolean held) =
    [1/2]this.owner_ |-> owner &*&
    [1/2]this.held |-> held;
  @*/

  public TicketlockStrong()
  //@ requires exists<list<int> >(?ns);
  //@ ensures [_]valid(ns) &*& state(0, false);
  //@ terminates;
  {
    owner = new AtomicLong();
    next = new AtomicLong();
    //@ this.ns = ns;
    //@ box growingListId = create_growing_list<int>();
    //@ this.growingListId = growingListId;
    //@ leak owner |-> _ &*& next |-> _ &*& this.ns |-> ns &*& this.growingListId |-> _;
    //@ close foreach({}, grabbed_cell);
    //@ close TicketlockStrong_inv(this)();
    //@ create_atomic_space_(ns, TicketlockStrong_inv(this));
  }

  public void acquire()
  /*@
  requires
    [_]valid(?ns) &*&
    is_TicketlockStrong_wait_ghost_op(?wop, this, ns, ?waitInv, currentThread) &*&
    is_TicketlockStrong_acquire_ghost_op(?ghop, this, ns, waitInv, ?post) &*&
    waitInv(-1, _);
  @*/
  //@ ensures held(?ticket) &*& post(ticket);
  //@ terminates;
  {
    //@ int callerThread = currentThread;
    //@ open valid(ns);
    //@ AtomicLong owner = this.owner;
    //@ AtomicLong next = this.next;
    //@ box growingListId = this.growingListId;
    //@ int cellId = create_ghost_cell(thread_info(waitInv, post, false));
    long ticket;
    {
      /*@
      predicate pre_() =
        [_]this.owner |-> owner &*&
        [_]this.next |-> next &*&
        [_]this.growingListId |-> growingListId &*&
        [_]this.ns |-> ns &*&
        [_]atomic_space_(ns, TicketlockStrong_inv(this)) &*&
        ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
        is_TicketlockStrong_acquire_ghost_op(ghop, this, ns, waitInv, post) &*& waitInv(-1, _);
      predicate post_(long result) =
        0 <= result &*&
        exists<boolean>(?alreadyOwner) &*&
        alreadyOwner ?
          post(result) &*& [1/2]owner.state(result) &*& [1/4]this.owner_ |-> result &*& [1/4]this.held |-> true
        :
          has_at(_, growingListId, result, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_getAndIncrement_ghost_op(next, pre_, post_)(op) {
        open pre_();
        open_atomic_space(ns, TicketlockStrong_inv(this));
        open TicketlockStrong_inv(this)();
        assert [_]owner.state(?owner_) &*& next.state(?next_);
        assert growing_list<int>(growingListId, ?cellIds);
        op();
        growing_list_add(growingListId, cellId);
        take_append(owner_, cellIds, {cellId});
        if (owner_ == next_) {
          predicate P() = [1/2]this.owner_ |-> owner_ &*& [1/2]held |-> false;
          predicate Q() = [1/2]this.owner_ |-> owner_ &*& [1/2]held |-> true;
          produce_lemma_function_pointer_chunk TicketlockStrong_acquire_op(this, owner_, P, Q)() {
            open P();
            open state(_, _);
            held = true;
            close state(owner_, true);
            close Q();
          } {
            close P();
            assert is_TicketlockStrong_acquire_op(?op_, _, _, _, _);
            ghop(owner_, op_);
            open Q();
          }
          close waiting_threads(this, ns, {}, owner_ + 1, owner_);
          ghost_cell_mutate(cellId, thread_info(waitInv, post, true));
          nth_append_r(cellIds, {cellId}, 0);
        } else if (owner_ < next_) {
          lemma void iter()
            requires
              waiting_threads(this, ns, ?cellIds0, ?index, owner_) &*& length(cellIds0) == length(cellIds) - index &*&
              [1/2]ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
              is_TicketlockStrong_acquire_ghost_op(ghop, this, ns, waitInv, post) &*&
              waitInv(-1, _);
            ensures
              waiting_threads(this, ns, append(cellIds0, {cellId}), index, owner_);
          {
            open waiting_threads(this, ns, cellIds0, index, owner_);
            switch (cellIds0) {
              case nil:
                close waiting_threads(this, ns, {}, index + 1, owner_);
              case cons(cellId0, cellIds00):
                iter();
            }
            close waiting_threads(this, ns, append(cellIds0, {cellId}), index, owner_);
          }
          length_drop(owner_ + 1, cellIds);
          drop_append_l(owner_ + 1, cellIds, {cellId});
          iter();
          create_has_at(growingListId, next_);
        } else {
        }
        close TicketlockStrong_inv(this)();
        close_atomic_space(ns, TicketlockStrong_inv(this));
        close exists(owner_ == next_);
        close post_(next_);
      };
      @*/
      //@ close pre_();
      ticket = this.next.getAndIncrement();
      //@ open post_(ticket);
    }
    for (;;)
    /*@
    invariant
      [_]this.owner |-> owner &*&
      [_]this.next |-> next &*&
      [_]this.ns |-> ns &*&
      [_]this.growingListId |-> growingListId &*&
      [_]atomic_space_(ns, TicketlockStrong_inv(this)) &*&
      exists(?alreadyOwner) &*&
      alreadyOwner ?
        post(ticket) &*& [1/2]owner.state(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
      :
        is_TicketlockStrong_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
        has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
    @*/
    {
      //@ open exists(alreadyOwner);
      long currentOwner;
      {
        /*@
        predicate pre_() =
          [_]this.owner |-> owner &*&
          [_]this.next |-> next &*& 
          [_]this.ns |-> ns &*&
          [_]this.growingListId |-> growingListId &*&
          [_]atomic_space_(ns, TicketlockStrong_inv(this)) &*&
          alreadyOwner ?
            post(ticket) &*& [1/2]owner.state(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            is_TicketlockStrong_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
        predicate post_(long result) =
          result == ticket ?
            post(ticket) &*& [1/2]owner.state(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            is_TicketlockStrong_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
            call_perm_(currentThread, TicketlockStrong.class) &*&
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(owner, pre_, post_)(op) {
          open pre_();
          open_atomic_space(ns, TicketlockStrong_inv(this));
          open TicketlockStrong_inv(this)();
          assert [_]owner.state(?owner_);
          assert growing_list(growingListId, ?cellIds);
          op();
          if (!alreadyOwner && owner_ == ticket) {
            match_has_at(growingListId);
            merge_fractions ghost_cell(cellId, _);
            ghost_cell_mutate(cellId, thread_info(waitInv, post, true));
          }
          if (owner_ != ticket) {
            predicate P() = [1/4]this.owner_ |-> owner_ &*& [1/4]this.held |-> true;
            produce_lemma_function_pointer_chunk TicketlockStrong_wait_op(this, owner_, P)() {
              open P();
              open this.state(_, _);
              close this.state(owner_, true);
              close P();
            } {
              match_has_at(growingListId);
              if (ticket < owner_) {
                foreach_remove_nth(ticket, take(owner_, cellIds));
                open grabbed_cell(_);
                nth_take(ticket, owner_, cellIds);
                merge_fractions ghost_cell(cellId, _);
                assert false;
              }
              close P();
              assert is_TicketlockStrong_wait_op(?op_, _, _, _);
              {
                lemma void iter()
                  requires
                    waiting_threads(this, ns, ?cellIds0, ?index, owner_) &*& 0 <= index &*& index <= ticket &*& ticket < index + length(cellIds0) &*&
                    cellIds0 == drop(index, cellIds) &*&
                    atomic_spaces({pair(ns, TicketlockStrong_inv(this))}) &*&
                    [1/2]ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
                    is_TicketlockStrong_wait_ghost_op(wop, this, ns, waitInv, callerThread) &*&
                    is_TicketlockStrong_wait_op(op_, this, owner_, P) &*& P();
                  ensures
                    waiting_threads(this, ns, cellIds0, index, owner_) &*& call_perm_(callerThread, TicketlockStrong.class) &*&
                    atomic_spaces({pair(ns, TicketlockStrong_inv(this))}) &*&
                    [1/2]ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
                    is_TicketlockStrong_wait_ghost_op(wop, this, ns, waitInv, callerThread) &*&
                    is_TicketlockStrong_wait_op(op_, this, owner_, P) &*& P();
                {
                  open waiting_threads(this, ns, cellIds0, index, owner_);
                  switch (cellIds0) {
                    case nil:
                      assert false;
                    case cons(cellId0, cellIds00):
                      if (index == ticket) {
                        nth_drop0(0, ticket, cellIds);
                        merge_fractions ghost_cell(cellId, _);
                        assert cellId0 == cellId;
                        wop(owner_, ticket - owner_, op_);
                      } else {
                        drop_n_plus_one(index, cellIds);
                        iter();
                      }
                  }
                  close waiting_threads(this, ns, cellIds0, index, owner_);
                }
                length_drop(owner_ + 1, cellIds);
                iter();
              }
              open P();
            }
          }
          close TicketlockStrong_inv(this)();
          close_atomic_space(ns, TicketlockStrong_inv(this));
          close post_(owner_);
        };
        @*/
        //@ close pre_();
        currentOwner = this.owner.get();
        //@ open post_(currentOwner);
      }
      if (currentOwner == ticket)
        break;
      //@ close exists(false);
    }
  }
  
  public boolean alone()
  //@ requires [_]valid(?ns) &*& held(?ticket) &*& is_TicketlockStrong_alone_ghost_op(?ghop, this, ns, ticket, ?pre, ?post) &*& pre();
  //@ ensures held(ticket) &*& result ? post() : pre() &*& TicketlockStrong_not_alone(this, ticket);
	//@ terminates;
  {
    AtomicLong next = this.next;
    //@ box growingListId = this.growingListId;
    long next_;
    //@ open valid(ns);
    {
      /*@
      predicate pre_() =
        is_TicketlockStrong_alone_ghost_op(ghop, this, ns, ticket, pre, post) &*& pre() &*&
        [_]this.owner |-> ?owner &*&
        [_]this.next |-> next &*&
        [_]this.ns |-> ns &*&
        [_]this.growingListId |-> growingListId &*&
        [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true &*&
        [_]atomic_space_(ns, TicketlockStrong_inv(this));
      predicate post_(long result) =
        [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true &*&
        0 <= result &*& 0 <= ticket &*& ticket < result &*&
        ticket + 1 < result ?
          pre() &*& TicketlockStrong_not_alone(this, ticket)
        :
          post();
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(this.next, pre_, post_)(op) {
        open pre_();
        open_atomic_space(ns, TicketlockStrong_inv(this));
        open TicketlockStrong_inv(this)();
        assert next.state(?next0);
        assert growing_list(growingListId, ?cellIds);
        op();
        if (ticket + 1 < next0) {
          create_has_at(growingListId, ticket + 1);
          close TicketlockStrong_not_alone(this, ticket);
        } else {
          predicate P() = [_]this.growingListId |-> growingListId &*& growing_list(growingListId, cellIds);
          produce_lemma_function_pointer_chunk TicketlockStrong_alone_op(this, ticket, P)() {
            open P();
            open TicketlockStrong_not_alone(this, ticket);
            match_has_at(growingListId);
            assert false;
          } {
            close P();
            assert is_TicketlockStrong_alone_op(?op_, _, _, _);
            ghop(op_);
            open P();
          }
        }
        close TicketlockStrong_inv(this)();
        close_atomic_space(ns, TicketlockStrong_inv(this));
        close post_(next0);
      };
      @*/
      //@ close pre_();
      next_ = this.next.get();
      //@ open post_(_);
    }
    return next_ - owner.getPlain() <= 1;
  }
  
  public void release()
  //@ requires [_]valid(?ns) &*& held(?ticket) &*& is_TicketlockStrong_release_ghost_op(?ghop, this, ns, ticket, ?pre, ?post) &*& pre();
  //@ ensures post();
  //@ terminates;
  {
    //@ open valid(ns);
    //@ open held(ticket);
    //@ AtomicLong owner = this.owner;
    //@ AtomicLong next = this.next;
    //@ box growingListId = this.growingListId;
    {
      /*@
      predicate pre_() =
        [_]this.owner |-> owner &*&
        [_]this.next |-> next &*&
        [_]this.ns |-> ns &*&
        [_]this.growingListId |-> growingListId &*&
        [1/2]owner.state(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true &*&
        [_]atomic_space_(ns, TicketlockStrong_inv(this)) &*&
        is_TicketlockStrong_release_ghost_op(ghop, this, ns, ticket, pre, post) &*& pre();
      predicate post_(long result) =
        post();
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_getAndIncrement_ghost_op(owner, pre_, post_)(op) {
        open pre_();
        open_atomic_space(ns, TicketlockStrong_inv(this));
        open TicketlockStrong_inv(this)();
        assert next.state(?next_);
        assert growing_list(growingListId, ?cellIds);
        op();
        {
          predicate P() = [1/2]this.owner_ |-> ticket &*& [1/2]held |-> true;
          predicate Q() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> false;
          produce_lemma_function_pointer_chunk TicketlockStrong_release_op(this, ticket, P, Q)() {
            open P();
            this.owner_++;
            this.held = false;
            close Q();
          } {
            close P();
            assert is_TicketlockStrong_release_op(?op_, _, _, _, _);
            ghop(op_);
            open Q();
          }
        }
        if (ticket + 1 < next_) {
          lemma void iter()
            requires waiting_threads(this, ns, ?cellIds0, ?index, ticket);
            ensures waiting_threads(this, ns, cellIds0, index, ticket + 1);
          {
            open waiting_threads(this, ns, cellIds0, index, ticket);
            switch (cellIds0) {
              case nil:
              case cons(cellId0, cellIds00):
                iter();
            }
            close waiting_threads(this, ns, cellIds0, index, ticket + 1);
          }
          open waiting_threads(this, _, _, _, _);
          drop_n_plus_one(ticket + 1, cellIds);
          iter();
          assert [1/2]ghost_cell(nth(ticket + 1, cellIds), thread_info(?pre1, ?post1, false));
          assert is_TicketlockStrong_acquire_ghost_op(?aop, this, ns, pre1, post1);
          {
            predicate P() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> false;
            predicate Q() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> true;
            produce_lemma_function_pointer_chunk TicketlockStrong_acquire_op(this, ticket + 1, P, Q)() {
              open P();
              held = true;
              close Q();
            } {
              close P();
              assert is_TicketlockStrong_acquire_op(?op_, _, _, _, _);
              aop(ticket + 1, op_);
              open Q();
            }
          }
        } else {
        }
        close foreach({}, grabbed_cell);
        close grabbed_cell(nth(ticket, cellIds));
        close foreach({nth(ticket, cellIds)}, grabbed_cell);
        foreach_append(take(ticket, cellIds), {nth(ticket, cellIds)});
        take_plus_one(ticket, cellIds);
        close TicketlockStrong_inv(this)();
        close_atomic_space(ns, TicketlockStrong_inv(this));
        close post_(ticket);
      };
      @*/
      //@ close pre_();
      this.owner.getAndIncrement();
      //@ open post_(_);
    }
  }
}
