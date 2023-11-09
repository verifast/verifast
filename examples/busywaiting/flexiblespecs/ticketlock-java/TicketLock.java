
/*@

typedef lemma void Ticketlock_wait_op(Ticketlock l, int owner_, predicate() P)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, held) &*& owner == owner_ &*& held &*& P();

typedef lemma void Ticketlock_wait_ghost_op(Ticketlock l, list<int> ns, predicate(int oldOwner, int oldM) waitInv, int callerThread)(int owner, int M, Ticketlock_wait_op *op);
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_wait_op(op, l, owner, ?P) &*& P() &*&
    0 <= owner &*& 0 <= M &*&
    waitInv(?oldOwner, ?oldM) &*&
    oldOwner == -1 || M < oldM || M == oldM && owner == oldOwner;
  ensures
    atomic_spaces(spaces) &*&
    is_Ticketlock_wait_op(op, l, owner, P) &*& P() &*&
    call_perm_(callerThread, Ticketlock.class) &*& waitInv(owner, M);

typedef lemma void Ticketlock_acquire_op(Ticketlock l, int owner_, predicate() P, predicate() Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, true) &*& owner == owner_ &*& !held &*& Q();

typedef lemma void Ticketlock_acquire_ghost_op(Ticketlock l, list<int> ns, predicate(int oldOwner, int oldM) waitInv, predicate(int) post)(int owner, Ticketlock_acquire_op *op);
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_acquire_op(op, l, owner, ?P, ?Q) &*& P() &*& 0 <= owner &*& waitInv(_, _);
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

inductive thread_info = thread_info(predicate(int, int) waitInv, predicate(int) post, boolean grabbed);

predicate waiting_threads(Ticketlock lock, list<int> ns, list<int> cellIds, int index, int owner) =
    switch (cellIds) {
        case nil: return true;
        case cons(cellId, cellIds0): return
            [1/2]ghost_cell(cellId, thread_info(?waitInv, ?post, false)) &*&
            is_Ticketlock_acquire_ghost_op(_, lock, ns, waitInv, post) &*&
            waitInv(?oldOwner, ?oldM) &*& oldOwner == -1 || index - owner < oldM || index - owner == oldM && owner == oldOwner &*&
            waiting_threads(lock, ns, cellIds0, index + 1, owner);
    };

predicate grabbed_cell(int cellId) = ghost_cell(cellId, thread_info(_, _, true));

predicate_ctor Ticketlock_inv(Ticketlock l)() =
  [_]l.ns |-> ?ns &*&
  [_]l.owner |-> ?owner_ &*& owner_.state(?owner) &*& 0 <= owner &*&
  [_]l.next |-> ?next_ &*& next_.state(?next) &*&
  [1/4]l.owner_ |-> owner &*& owner <= next &*&
  [1/4]l.held |-> ?held &*&
  [_]l.growingListId |-> ?growingListId &*& growing_list<int>(growingListId, ?cellIds) &*& length(cellIds) == next &*&
  foreach(take(owner, cellIds), grabbed_cell) &*&
  owner < next ?
    waiting_threads(l, ns, drop(owner + 1, cellIds), owner + 1, owner) &*&
    [1/2]ghost_cell(nth(owner, cellIds), thread_info(?waitInv, ?post, ?grabbed)) &*&
    (grabbed ? [1/2]ghost_cell<thread_info>(nth(owner, cellIds), _) : post(owner) &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> true) &*&
    held
  :
    !held &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> false;

@*/

public final class Ticketlock {
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
    atomic_space_(ns, Ticketlock_inv(this));
  @*/
  
  /*@
  predicate held(long ticket) =
    [1/4]owner_ |-> ticket &*&
    [1/4]held |-> true &*&
    [_]growingListId |-> ?growingListId;
  @*/
  
  /*@
  predicate state(int owner, boolean held) =
    [1/2]this.owner_ |-> owner &*&
    [1/2]this.held |-> held;
  @*/

  public Ticketlock()
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
    //@ close Ticketlock_inv(this)();
    //@ create_atomic_space_(ns, Ticketlock_inv(this));
  }

  public void acquire()
  /*@
  requires
    [_]valid(?ns) &*&
    is_Ticketlock_wait_ghost_op(?wop, this, ns, ?waitInv, currentThread) &*&
    is_Ticketlock_acquire_ghost_op(?ghop, this, ns, waitInv, ?post) &*&
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
        [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
        ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
        is_Ticketlock_acquire_ghost_op(ghop, this, ns, waitInv, post) &*& waitInv(-1, _);
      predicate post_(long result) =
        0 <= result &*&
        exists<boolean>(?alreadyOwner) &*&
        alreadyOwner ?
          post(result) &*& [1/4]this.owner_ |-> result &*& [1/4]this.held |-> true
        :
          has_at(_, growingListId, result, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_getAndIncrement_ghost_op(next, pre_, post_)(op) {
        open pre_();
        open_atomic_space(ns, Ticketlock_inv(this));
        open Ticketlock_inv(this)();
        assert owner.state(?owner_) &*& next.state(?next_);
        assert growing_list<int>(growingListId, ?cellIds);
        op();
        growing_list_add(growingListId, cellId);
        take_append(owner_, cellIds, {cellId});
        if (owner_ == next_) {
          predicate P() = [1/2]this.owner_ |-> owner_ &*& [1/2]held |-> false;
          predicate Q() = [1/2]this.owner_ |-> owner_ &*& [1/2]held |-> true;
          produce_lemma_function_pointer_chunk Ticketlock_acquire_op(this, owner_, P, Q)() {
            open P();
            open state(_, _);
            held = true;
            close state(owner_, true);
            close Q();
          } {
            close P();
            assert is_Ticketlock_acquire_op(?op_, _, _, _, _);
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
              is_Ticketlock_acquire_ghost_op(ghop, this, ns, waitInv, post) &*&
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
        close Ticketlock_inv(this)();
        close_atomic_space(ns, Ticketlock_inv(this));
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
      [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
      exists(?alreadyOwner) &*&
      alreadyOwner ?
        post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
      :
        is_Ticketlock_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
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
          [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
          alreadyOwner ?
            post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            is_Ticketlock_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
        predicate post_(long result) =
          result == ticket ?
            post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            is_Ticketlock_wait_ghost_op(wop, this, ns, waitInv, currentThread) &*&
            call_perm_(currentThread, Ticketlock.class) &*&
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(waitInv, post, false));
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(owner, pre_, post_)(op) {
          open pre_();
          open_atomic_space(ns, Ticketlock_inv(this));
          open Ticketlock_inv(this)();
          assert owner.state(?owner_);
          assert growing_list(growingListId, ?cellIds);
          op();
          if (!alreadyOwner && owner_ == ticket) {
            match_has_at(growingListId);
            merge_fractions ghost_cell(cellId, _);
            ghost_cell_mutate(cellId, thread_info(waitInv, post, true));
          }
          if (owner_ != ticket) {
            predicate P() = [1/4]this.owner_ |-> owner_ &*& [1/4]this.held |-> true;
            produce_lemma_function_pointer_chunk Ticketlock_wait_op(this, owner_, P)() {
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
              assert is_Ticketlock_wait_op(?op_, _, _, _);
              {
                lemma void iter()
                  requires
                    waiting_threads(this, ns, ?cellIds0, ?index, owner_) &*& 0 <= index &*& index <= ticket &*& ticket < index + length(cellIds0) &*&
                    cellIds0 == drop(index, cellIds) &*&
                    atomic_spaces({pair(ns, Ticketlock_inv(this))}) &*&
                    [1/2]ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
                    is_Ticketlock_wait_ghost_op(wop, this, ns, waitInv, callerThread) &*&
                    is_Ticketlock_wait_op(op_, this, owner_, P) &*& P();
                  ensures
                    waiting_threads(this, ns, cellIds0, index, owner_) &*& call_perm_(callerThread, Ticketlock.class) &*&
                    atomic_spaces({pair(ns, Ticketlock_inv(this))}) &*&
                    [1/2]ghost_cell(cellId, thread_info(waitInv, post, false)) &*&
                    is_Ticketlock_wait_ghost_op(wop, this, ns, waitInv, callerThread) &*&
                    is_Ticketlock_wait_op(op_, this, owner_, P) &*& P();
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
          close Ticketlock_inv(this)();
          close_atomic_space(ns, Ticketlock_inv(this));
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

  public void release()
  //@ requires [_]valid(?ns) &*& held(?ticket) &*& is_Ticketlock_release_ghost_op(?ghop, this, ns, ticket, ?pre, ?post) &*& pre();
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
        [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true &*&
        [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
        is_Ticketlock_release_ghost_op(ghop, this, ns, ticket, pre, post) &*& pre();
      predicate post_(long result) =
        post();
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_getAndIncrement_ghost_op(owner, pre_, post_)(op) {
        open pre_();
        open_atomic_space(ns, Ticketlock_inv(this));
        open Ticketlock_inv(this)();
        assert next.state(?next_);
        assert growing_list(growingListId, ?cellIds);
        op();
        {
          predicate P() = [1/2]this.owner_ |-> ticket &*& [1/2]held |-> true;
          predicate Q() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> false;
          produce_lemma_function_pointer_chunk Ticketlock_release_op(this, ticket, P, Q)() {
            open P();
            this.owner_++;
            this.held = false;
            close Q();
          } {
            close P();
            assert is_Ticketlock_release_op(?op_, _, _, _, _);
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
          assert is_Ticketlock_acquire_ghost_op(?aop, this, ns, pre1, post1);
          {
            predicate P() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> false;
            predicate Q() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> true;
            produce_lemma_function_pointer_chunk Ticketlock_acquire_op(this, ticket + 1, P, Q)() {
              open P();
              held = true;
              close Q();
            } {
              close P();
              assert is_Ticketlock_acquire_op(?op_, _, _, _, _);
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
        close Ticketlock_inv(this)();
        close_atomic_space(ns, Ticketlock_inv(this));
        close post_(ticket);
      };
      @*/
      //@ close pre_();
      this.owner.getAndIncrement();
      //@ open post_(_);
    }
  }
}
