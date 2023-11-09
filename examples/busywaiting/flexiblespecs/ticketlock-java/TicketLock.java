
/*@

typedef lemma void Ticketlock_acquire_op(Ticketlock l, predicate() P, predicate(int) Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, true) &*& Q(owner);

typedef lemma void Ticketlock_acquire_ghost_op(Ticketlock l, list<int> ns, predicate() pre, predicate(int) post)();
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_acquire_op(?op, l, ?P, ?Q) &*& P() &*& pre();
  ensures
    atomic_spaces(spaces) &*&
    is_Ticketlock_acquire_op(op, l, P, Q) &*& Q(?ticket) &*& post(ticket);

typedef lemma void Ticketlock_release_op(Ticketlock l, long ticket, predicate() P, predicate() Q)();
  requires l.state(ticket, true) &*& P();
  ensures l.state(ticket + 1, false) &*& Q();

typedef lemma void Ticketlock_release_ghost_op(Ticketlock l, list<int> ns, long ticket, predicate() pre, predicate() post)();
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_Ticketlock_release_op(?op, l, ticket, ?P, ?Q) &*& P() &*& pre();
  ensures
    atomic_spaces(spaces) &*&
    is_Ticketlock_release_op(op, l, ticket, P, Q) &*& Q() &*& post();

inductive thread_info = thread_info(predicate() pre, predicate(int) post, boolean grabbed);

predicate waiting_threads(Ticketlock lock, list<int> ns, list<int> cellIds, int index, int owner) =
    switch (cellIds) {
        case nil: return true;
        case cons(cellId, cellIds0): return
            [1/2]ghost_cell(cellId, thread_info(?pre, ?post, false)) &*&
            is_Ticketlock_acquire_ghost_op(_, lock, ns, pre, post) &*&
            pre() &*&
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
  //foreach(take(owner, cellIds), grabbed_cell) &*&
  owner < next ?
    waiting_threads(l, ns, drop(owner + 1, cellIds), owner + 1, owner) &*&
    [1/2]ghost_cell(nth(owner, cellIds), thread_info(?pre, ?post, ?grabbed)) &*&
    (grabbed ? true : post(owner) &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> true) &*&
    held
  :
    !held &*& [1/4]l.owner_ |-> owner &*& [1/4]l.held |-> false;

@*/

public final class Ticketlock {
  private AtomicLong owner = new AtomicLong();
  private AtomicLong next = new AtomicLong();
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
  
  //@ predicate held(long ticket) = [1/4]owner_ |-> ticket &*& [1/4]held |-> true;

  /*@
  predicate state(int owner, boolean held) =
    [1/2]this.owner_ |-> owner &*&
    [1/2]this.held |-> held;
  @*/

  public Ticketlock()
  //@ requires exists<list<int> >(?ns);
  //@ ensures [_]valid(ns) &*& state(0, false);
  {
    //@ this.ns = ns;
    //@ box growingListId = create_growing_list<int>();
    //@ this.growingListId = growingListId;
    //@ leak owner |-> _ &*& next |-> _ &*& this.ns |-> ns &*& this.growingListId |-> _;
    //@ close foreach({}, grabbed_cell);
    //@ close Ticketlock_inv(this)();
    //@ create_atomic_space_(ns, Ticketlock_inv(this));
  }

  public void acquire()
  //@ requires [_]valid(?ns) &*& is_Ticketlock_acquire_ghost_op(?ghop, this, ns, ?pre, ?post) &*& pre();
  //@ ensures held(?ticket) &*& post(ticket);
  {
    //@ open valid(ns);
    //@ AtomicLong owner = this.owner;
    //@ AtomicLong next = this.next;
    //@ box growingListId = this.growingListId;
    //@ int cellId = create_ghost_cell(thread_info(pre, post, false));
    long ticket;
    {
      /*@
      predicate pre_() =
        [_]this.owner |-> owner &*&
        [_]this.next |-> next &*&
        [_]this.growingListId |-> growingListId &*&
        [_]this.ns |-> ns &*&
        [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
        ghost_cell(cellId, thread_info(pre, post, false)) &*&
        is_Ticketlock_acquire_ghost_op(ghop, this, ns, pre, post) &*& pre();
      predicate post_(long result) =
        exists<boolean>(?alreadyOwner) &*&
        alreadyOwner ?
          post(result) &*& [1/4]this.owner_ |-> result &*& [1/4]this.held |-> true
        :
          has_at(_, growingListId, result, cellId) &*& [1/2]ghost_cell(cellId, thread_info(pre, post, false));
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
          predicate Q(int result) = [1/2]this.owner_ |-> owner_ &*& [1/2]held |-> true &*& result == owner_;
          produce_lemma_function_pointer_chunk Ticketlock_acquire_op(this, P, Q)() {
            open P();
            open state(_, _);
            held = true;
            close state(owner_, true);
            close Q(owner_);
          } {
            close P();
            ghop();
            open Q(_);
          }
          close waiting_threads(this, ns, {}, owner_ + 1, owner_);
          ghost_cell_mutate(cellId, thread_info(pre, post, true));
        } else if (owner_ < next_) {
          lemma void iter()
            requires
              waiting_threads(this, ns, ?cellIds0, ?index, owner_) &*& length(cellIds0) == length(cellIds) - index &*&
              [1/2]ghost_cell(cellId, thread_info(pre, post, false)) &*&
              is_Ticketlock_acquire_ghost_op(ghop, this, ns, pre, post) &*&
              pre();
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
      [_]this.growingListId |-> growingListId &*&
      [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
      exists(?alreadyOwner) &*&
      alreadyOwner ?
        post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
      :
        has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(pre, post, false));
    @*/
    {
      //@ open exists(alreadyOwner);
      long currentOwner;
      {
        /*@
        predicate pre_() =
          [_]this.owner |-> owner &*&
          [_]this.next |-> next &*& 
          [_]this.growingListId |-> growingListId &*&
          [_]atomic_space_(ns, Ticketlock_inv(this)) &*&
          alreadyOwner ?
            post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(pre, post, false));
        predicate post_(long result) =
          result == ticket ?
            post(ticket) &*& [1/4]this.owner_ |-> ticket &*& [1/4]held |-> true
          :
            has_at(?cellHandle, growingListId, ticket, cellId) &*& [1/2]ghost_cell(cellId, thread_info(pre, post, false));
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(owner, pre_, post_)(op) {
          open pre_();
          open_atomic_space(ns, Ticketlock_inv(this));
          open Ticketlock_inv(this)();
          assert owner.state(?owner_);
          op();
          if (!alreadyOwner && owner_ == ticket) {
            match_has_at(growingListId);
            merge_fractions ghost_cell(cellId, _);
            ghost_cell_mutate(cellId, thread_info(pre, post, true));
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
            ghop();
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
          assert growing_list(growingListId, ?cellIds);
          drop_n_plus_one(ticket + 1, cellIds);
          iter();
          assert [1/2]ghost_cell(nth(ticket + 1, cellIds), thread_info(?pre1, ?post1, false));
          assert is_Ticketlock_acquire_ghost_op(?aop, this, ns, pre1, post1);
          {
            predicate P() = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> false;
            predicate Q(int result) = [1/2]this.owner_ |-> ticket + 1 &*& [1/2]held |-> true &*& result == ticket + 1;
            produce_lemma_function_pointer_chunk Ticketlock_acquire_op(this, P, Q)() {
              open P();
              held = true;
              close Q(ticket + 1);
            } {
              close P();
              aop();
              open Q(_);
            }
          }
        } else {
        }
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
