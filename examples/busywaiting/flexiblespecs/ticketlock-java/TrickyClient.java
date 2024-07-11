// tab_size:2

/*@

fixpoint level L(int k) { return level(Client.class, {1 + Spinlock_level_nb_dims, k}); }

predicate Client_inv() =
  [_]Client.lk |-> ?_lk &*& _lk.state(?b) &*& Client_inv_(b);
  
predicate done_value(long d) = true;

predicate Client_inv_(boolean b) =
  [_]Client.done |-> ?_done &*& done_value(?d) &*& [1/2]Client.main_set_done |-> ?mainSetDone &*&
  (
		!b ?
		  Client.lockOwner |-> none
		:
		  [1/2]Client.lockOwner |-> some(?thread1HoldsLock) &*&
		  thread1HoldsLock ?
		    [_]Client.l1 |-> ?_l1 &*& signal(_l1, L(0), false)
		  :
		    d == 0 ?
		      [1/2]Client.l22_created |-> false &*&
		      [1/2]Client.l21 |-> ?_l21 &*& signal(_l21, L(0), false)
		    :
		      [1/2]Client.l22_created |-> ?l22Created &*&
		      !l22Created ?
		        [_]Client.l21 |-> ?_l21 &*& signal(_l21, L(0), false)
		      :
		        [_]Client.l22 |-> ?_l22 &*& signal(_l22, L(0), false)
  ) &*&
  (
    d == 0 ?
      _done.state(0)
    :
      d == 1 &*& [_]_done.state(1)
  ) &*&
  (
    !mainSetDone ?
      [_]Client.s3 |-> ?_s3 &*& signal(_s3, L(0), false)
    :
      d == 1
  );

predicate started_waiting(boolean b) = true;

predicate waiting_for_s3(boolean b) = true;

predicate waiting_for_l21(boolean b, list<pathcomp> p) =
  b ?
    [_]Client.l21 |-> ?_l21 &*& wait_perm(p, _l21, L(0), Spinlock.class)
  :
    call_below_perm(p, Client.class);
            
predicate waiting_for_l22(boolean b, list<pathcomp> p) =
  b ?
    [_]Client.l22 |-> ?_l22 &*& wait_perm(p, _l22, L(0), Spinlock.class)
  :
    call_below_perm(p, Client.class);

predicate seen_done_set(boolean b) = true;

lemma void AtomicLong_state_merge_fractions(AtomicLong l)
  requires [?f1]l.state(?d1) &*& [?f2]l.state(?d2);
  ensures [f1 + f2]l.state(d1) &*& d2 == d1;
{
}

@*/

class Client {

  static Spinlock lk;
  static AtomicLong done;
  
  //@ static option<boolean> lockOwner;
  //@ static boolean main_set_done;
  //@ static void *s3 = default_value;
  //@ static void *l1 = default_value;
  //@ static void *l21 = default_value; // Signal created by thread 2 at a point when done was still 0
  //@ static boolean l22_created = false;
  //@ static void *l22 = default_value; // Signal created by thread 2 at a point when done was already 1
  
  static void thread1()
  /*@
  requires
    obs(currentThread, ?p, {}) &*&
    [_]atomic_space_({1}, Client_inv) &*&
    [_]lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
    [_]Client.done |-> ?_done &*& _done != null &*&
    [_]Client.s3 |-> ?_s3 &*&
    Client.l1 |-> _;
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ create_wait_perm(_s3, L(0), Spinlock.class);
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    {
      /*@
      predicate waitInv() =
				[_]atomic_space_({1}, Client_inv) &*&
				[_]lk |-> _lk &*& [_]_lk.valid({0}, L(0)) &*&
				Client.l1 |-> _ &*&
        [_]Client.done |-> _done &*&
        [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Spinlock.class) &*&
        waiting_for_l21(_, p) &*&
        waiting_for_l22(_, p);
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*& Client_inv_(held) &*&
				[_]atomic_space_({1}, Client_inv) &*&
				[_]lk |-> _lk &*& [_]_lk.valid({0}, L(0)) &*&
				Client.l1 |-> _ &*&
        [_]Client.done |-> _done &*&
        [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Spinlock.class) &*&
        waiting_for_l21(_, p) &*&
        waiting_for_l22(_, p);
      predicate post() =
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.l1 |-> ?_l1 &*&
        obs(currentThread, p, {pair(_l1, L(0))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_sep(_lk, {0}, waitInv, R)() {
        open waitInv();
        assert atomic_spaces(?spaces);
        if (mem(pair({1}, Client_inv), spaces)) {
          mem_map(pair({1}, Client_inv), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
          assert false;
        }
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        close R(spaces, _);
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_wait_ghost_op(_lk, R, currentThread, p, L(0), waitInv)() {
        open R(?spaces, true);
        open Client_inv_(true);
        assert [_]_done.state(?d);
        is_ancestor_of_refl(p);
        if (d == 0) {
          wait(_s3);
        } else {
          assert [_]Client.l22_created |-> ?l22Created;
          if (!l22Created) {
            open waiting_for_l21(?waitingForL21, p);
            assert [_]Client.l21 |-> ?_l21;
            if (!waitingForL21) {
              create_wait_perm(_l21, L(0), Spinlock.class);
              open exists(false);
              close exists(true);
            }
            wait(_l21);
            close waiting_for_l21(true, p);
          } else {
            open waiting_for_l22(?waitingForL22, p);
            assert [_]Client.l22 |-> ?_l22;
            if (!waitingForL22) {
              create_wait_perm(_l22, L(0), Spinlock.class);
            }
            wait(_l22);
            close waiting_for_l22(true, p);
          }
        }
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv); 
        close waitInv();
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_acquire_ghost_op(_lk, R, p, {}, post, currentThread)() {
        open R(?spaces, false);
        open Client_inv_(false);
        Client.lockOwner = some(true);
        void *_l1 = create_signal();
        init_signal(_l1, L(0));
        Client.l1 = _l1;
        leak Client.l1 |-> _l1;
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close waiting_for_l21(false, p);
      //@ close waiting_for_l22(false, p);
      //@ close waitInv();
      lk.acquire();
      //@ open post();
    }
    //@ void *_l1 = Client.l1;
    {
      /*@
      predicate pre() =
        [_]Client.done |-> _done &*&
        [_]atomic_space_({1}, Client_inv);
      predicate post() =
        true;
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_set_ghost_op(_done, 1, pre, post)(op) {
        open pre();
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        open Client_inv_(?held);
        assert [_]_done.state(?d);
        op();
        if (d == 0) {
          open done_value(0);
          close done_value(1);
        }
        close Client_inv_(held);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close pre();
      done.set(1);
      //@ open post();
    }
    {
      /*@
      predicate pre() =
        obs(currentThread, p, {pair(_l1, L(0))}) &*&
        [_]Client.l1 |-> _l1 &*&
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.lk |-> _lk &*&
        [_]atomic_space_({1}, Client_inv);
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        obs(currentThread, p, {pair(_l1, L(0))}) &*&
        [_]Client.l1 |-> _l1 &*&
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.lk |-> _lk &*&
        atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*&
        Client_inv_(held);
      predicate post(list<pathcomp> _p, list<pair<void *, level> > obs) =
        _p == p &*& obs == {};
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_sep(_lk, {0}, pre, R)() {
        open pre();
        assert atomic_spaces(?spaces);
        if (mem(pair({1}, Client_inv), spaces)) {
          mem_map(pair({1}, Client_inv), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
          assert false;
        }
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        close R(spaces, _);
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_release_ghost_op(_lk, R, post, currentThread)() {
        open R(?spaces, true);
        open Client_inv_(true);
        Client.lockOwner = none;
        set_signal(_l1);
        close Client_inv_(false);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post(p, {});
      };
      @*/
      //@ close pre();
      lk.release();
      //@ open post(_, _);
    }
  }
  
  static void thread2()
  /*@
  requires
    [_]Client.s3 |-> ?_s3 &*&
    [_]atomic_space_({1}, Client_inv) &*&
    Client.l21 |-> _ &*&
    Client.l22_created |-> false &*&
    Client.l22 |-> _ &*&
    [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
    [_]Client.done |-> ?_done &*& _done != null &*&
    obs(currentThread, ?p, {}) &*&
    call_below_perm(p, Program.class) &*&
    call_perm_(currentThread, Client.class);
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ create_wait_perm(_s3, L(0), Client.class);
    //@ close seen_done_set(false);
    for (;;)
    /*@
    invariant
      [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Client.class) &*&
      [_]atomic_space_({1}, Client_inv) &*&
      Client.l22_created |-> false &*& Client.l22 |-> _ &*&
      seen_done_set(?seenDoneSet) &*&
      (
        !seenDoneSet ?
          call_perm_(currentThread, Client.class) &*&
          Client.l21 |-> _
        :
          [_]_done.state(1)
      ) &*&
		  [_]Client.lk |-> _lk &*& [_]_lk.valid({0}, L(0)) &*&
		  [_]Client.done |-> _done &*& _done != null &*&
		  obs(currentThread, p, {});
    @*/
    {
      {
        /*@
        predicate waitInv() =
          [_]atomic_space_({1}, Client_inv) &*&
				  Client.l22_created |-> false &*& Client.l22 |-> _ &*&
				  seen_done_set(seenDoneSet) &*&
				  (
				    !seenDoneSet ?
				      Client.l21 |-> _
				    :
				      [_]_done.state(1)
				  ) &*&
          [_]Client.lk |-> _lk &*&
    		  [_]Client.done |-> _done &*& _done != null &*&
          [_]atomic_space_({1}, Client_inv) &*&
          started_waiting(?startedWaiting) &*&
          !startedWaiting ?
            call_below_perm(p, Client.class)
          :
            [_]Client.l1 |-> ?_l1 &*& wait_perm(p, _l1, L(0), Spinlock.class);
        predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
          [_]atomic_space_({1}, Client_inv) &*&
				  Client.l22_created |-> false &*& Client.l22 |-> _ &*&
				  seen_done_set(seenDoneSet) &*&
				  (
				    !seenDoneSet ?
				      Client.l21 |-> _
				    :
				      [_]_done.state(1)
				  ) &*&
          [_]Client.lk |-> _lk &*&
    		  [_]Client.done |-> _done &*& _done != null &*&
          atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*& Client_inv_(held) &*&
          started_waiting(?startedWaiting) &*&
          !startedWaiting ?
            call_below_perm(p, Client.class)
          :
            [_]Client.l1 |-> ?_l1 &*& wait_perm(p, _l1, L(0), Spinlock.class);
        predicate post() =
          [1/2]lockOwner |-> some(false) &*&
				  [1/2]Client.l22_created |-> ?l22Created &*&
				  (
				    !l22Created ?
				      [1/2]Client.l21 |-> ?_l21 &*& obs(currentThread, p, {pair(_l21, L(0))}) &*& Client.l22 |-> _
				    :
				      [_]_done.state(1) &*& [_]Client.l22 |-> ?_l22 &*& obs(currentThread, p, {pair(_l22, L(0))})
				  );
        @*/
        /*@
        produce_lemma_function_pointer_chunk Spinlock_sep(_lk, {0}, waitInv, R)() {
		      open waitInv();
		      assert atomic_spaces(?spaces);
		      if (mem(pair({1}, Client_inv), spaces)) {
		        mem_map(pair({1}, Client_inv), spaces, fst);
		        forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
		        assert false;
		      }
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      close R(spaces, _);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk Spinlock_wait_ghost_op(_lk, R, currentThread, p, L(0), waitInv)() {
          open R(?spaces, _);
          open Client_inv_(true);
          assert started_waiting(?startedWaiting);
          assert [_]Client.l1 |-> ?_l1;
          if (!startedWaiting) {
            create_wait_perm(_l1, L(0), Spinlock.class);
            open started_waiting(false);
            close started_waiting(true);
          }
          assert done_value(?d);
          assert seen_done_set(?seenDoneSet1);
          if (d == 0 && seenDoneSet1)
            AtomicLong_state_merge_fractions(_done);
          is_ancestor_of_refl(p);
          wait(_l1);
          close Client_inv_(true);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close waitInv();
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk Spinlock_acquire_ghost_op(_lk, R, p, {}, post, currentThread)() {
          open R(?spaces, _);
          open Client_inv_(false);
          Client.lockOwner = some(false);
          assert done_value(?d);
          open seen_done_set(?seenDoneSet1);
          if (d == 0 && seenDoneSet1)
            AtomicLong_state_merge_fractions(_done);
          if (d == 0) {
            void *l21 = create_signal();
            init_signal(l21, L(0));
            Client.l21 = l21;
            close seen_done_set(false);
          } else {
            Client.l22_created = true;
            void *l22 = create_signal();
            init_signal(l22, L(0));
            Client.l22 = l22;
            leak Client.l22 |-> l22;
            close seen_done_set(true);
          }
          close Client_inv_(true);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close post();
        };
        @*/
        //@ close started_waiting(false);
        //@ produce_call_below_perm_();
        //@ pathize_call_below_perm_();
        //@ close waitInv();
        lk.acquire();
        //@ open post();
      }
      //@ boolean l22Created = Client.l22_created;
      long value;
      {
        /*@
        predicate pre() =
          [1/2]Client.l22_created |-> l22Created &*&
          (
            !l22Created ?
              true
            :
              [_]_done.state(1)
          ) &*&
          [_]Client.done |-> _done &*&
          (!seenDoneSet ? true : [_]_done.state(1)) &*&
          [_]atomic_space_({1}, Client_inv);
        predicate post(long result) =
          [1/2]Client.l22_created |-> l22Created &*& 
          result == 0 ?
            !l22Created &*& !seenDoneSet
          :
            [_]_done.state(1);
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(_done, pre, post)(op) {
          open pre();
          open_atomic_space({1}, Client_inv);
          open Client_inv();
          open Client_inv_(?held);
          assert [_]_done.state(?d);
          if (d == 0 && (l22Created || seenDoneSet))
            AtomicLong_state_merge_fractions(_done);
          op();
          close Client_inv_(held);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close post(d);
        };
        @*/
        //@ close pre();
        value = done.get();
        //@ open post(_);
      }
      {
        /*@
        predicate pre() =
          [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Client.class) &*&
          [1/2]Client.l22_created |-> l22Created &*&
          (
            !l22Created ?
              [1/2]Client.l21 |-> ?_l21 &*& obs(currentThread, p, {pair(_l21, L(0))})
            :
              [_]Client.l22 |-> ?_l22 &*& obs(currentThread, p, {pair(_l22, L(0))})
          ) &*&
          [1/2]Client.lockOwner |-> some(false) &*&
          [_]Client.lk |-> _lk &*& [_]Client.done |-> _done &*& (!seenDoneSet ? true : [_]_done.state(1)) &*&
          [_]atomic_space_({1}, Client_inv);
        predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
          [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Client.class) &*&
          [1/2]Client.l22_created |-> l22Created &*&
          (
            !l22Created ?
              [1/2]Client.l21 |-> ?_l21 &*& obs(currentThread, p, {pair(_l21, L(0))})
            :
              [_]Client.l22 |-> ?_l22 &*& obs(currentThread, p, {pair(_l22, L(0))})
          ) &*&
          [1/2]Client.lockOwner |-> some(false) &*&
          [_]Client.lk |-> _lk &*& [_]Client.done |-> _done &*& (!seenDoneSet ? true : [_]_done.state(1)) &*&
          [_]atomic_space_({1}, Client_inv) &*&
          atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*& Client_inv_(held);
        predicate post(list<pathcomp> _p, list<pair<void *, level> > obs) =
          [_]Client.s3 |-> _s3 &*& wait_perm(p, _s3, L(0), Client.class) &*&
          l22_created |-> l22Created &*&
          seen_done_set(?seenDoneSet1) &*&
          (
            !seenDoneSet1 ?
              !seenDoneSet &*&
              l21 |-> _ &*& call_perm_(currentThread, Client.class)
            :
              [_]_done.state(1)
          ) &*&
          _p == p &*& obs == {};
        @*/
        /*@
        produce_lemma_function_pointer_chunk Spinlock_sep(_lk, {0}, pre, R)() {
		      open pre();
		      assert atomic_spaces(?spaces);
		      if (mem(pair({1}, Client_inv), spaces)) {
		        mem_map(pair({1}, Client_inv), spaces, fst);
		        forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
		        assert false;
		      }
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      close R(spaces, _);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk Spinlock_release_ghost_op(_lk, R, post, currentThread)() {
          open R(?spaces, _);
          open Client_inv_(true);
          Client.lockOwner = none;
          if (!l22Created) {
            assert [_]Client.l21 |-> ?_l21;
          	set_signal(_l21);
          } else {
            assert [_]Client.l22 |-> ?_l22;
            set_signal(_l22);
          }
        	assert done_value(?d);
        	if (d == 0) {
        	  if (seenDoneSet)
        	    AtomicLong_state_merge_fractions(_done);
        	  is_ancestor_of_refl(p);
        	  wait(_s3);
        	}
        	close seen_done_set(d != 0);
          close Client_inv_(false);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close post(p, {});
        };
        @*/
        //@ close pre();
        lk.release();
        //@ open post(_, _);
      }
      if (value != 0)
        break;
    }
  }
  
  static void thread3()
  /*@
  requires
    [1/2]Client.main_set_done |-> false &*&
    [_]atomic_space_({1}, Client_inv) &*&
    [_]done |-> ?_done &*& _done != null &*&
    [_]s3 |-> ?_s3 &*&
    obs(currentThread, ?p, {pair(_s3, L(0))});
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    {
      /*@
      predicate pre() =
        [1/2]Client.main_set_done |-> false &*&
				[_]atomic_space_({1}, Client_inv) &*&
				[_]done |-> _done &*& _done != null &*&
				[_]s3 |-> _s3 &*&
				obs(currentThread, p, {pair(_s3, L(0))});
      predicate post() =
        obs(currentThread, p, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_set_ghost_op(_done, 1, pre, post)(op) {
        open pre();
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        open Client_inv_(?held);
        op();
        Client.main_set_done = true;
        assert done_value(?d);
        if (d == 0) {
          open done_value(0);
          close done_value(1);
        }
        set_signal(_s3);
        close Client_inv_(held);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close pre();
      done.set(1);
      //@ open post();
    }
  }

  static void main()
  /*@
  requires
    obs(currentThread, {}, {}) &*&
    class_init_token(Client.class) &*&
    call_perm_(currentThread, Thread1.class) &*&
    call_perm_(currentThread, Thread2.class) &*&
    call_below_perm({}, Program.class);
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ init_class(Client.class);
    //@ close exists(pair({0}, L(0)));
    lk = new Spinlock();
    //@ leak Client.lk |-> _;
    done = new AtomicLong();
    //@ leak Client.done |-> _;
    //@ void *_s3 = create_signal();
    //@ init_signal(_s3, L(0));
    //@ Client.s3 = _s3;
    //@ leak Client.s3 |-> _;
    //@ close done_value(0);
    //@ Client.lockOwner = none;
    //@ close Client_inv_(false);
    //@ close Client_inv();
    //@ create_atomic_space_({1}, Client_inv);
    //@ leak atomic_space_({1}, Client_inv);
    
    Thread1 thread1 = new Thread1();
    {
      /*@
      predicate pre() =
				[_]atomic_space_({1}, Client_inv) &*&
				[_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
				[_]Client.done |-> ?_done &*& _done != null &*&
				[_]Client.s3 |-> _s3 &*&
				Client.l1 |-> _;
      predicate post() = obs(currentThread, {Forker}, {pair(_s3, L(0))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {}, {pair(_s3, L(0))}, {pair(_s3, L(0))}, thread1, pre, post)(forkeeId) {
        open pre();
        close post();
        close Runnable_pre(Thread1.class)(thread1, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(thread1).start();
      //@ open post();
    }
    
    Thread2 thread2 = new Thread2();
    {
      /*@
      predicate pre() =
				[_]Client.s3 |-> _s3 &*&
				[_]atomic_space_({1}, Client_inv) &*&
				Client.l21 |-> _ &*&
				Client.l22_created |-> false &*&
				Client.l22 |-> _ &*&
				[_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
				[_]Client.done |-> ?_done &*& _done != null &*&
				call_below_perm({}, Program.class);
      predicate post() = obs(currentThread, {Forker, Forker}, {pair(_s3, L(0))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {Forker}, {pair(_s3, L(0))}, {pair(_s3, L(0))}, thread2, pre, post)(forkeeId) {
        open pre();
        close post();
        call_below_perm_weaken_path({Forkee, Forker});
        
        close Runnable_pre(Thread2.class)(thread2, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(thread2).start();
      //@ open post();
    }
    
    thread3();
  }
  
}

/*@

predicate_family_instance Runnable_pre(Thread1.class)(Thread1 thread1, int threadId) =
  obs(threadId, ?p, {}) &*&
  [_]atomic_space_({1}, Client_inv) &*&
  [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
  [_]Client.done |-> ?_done &*& _done != null &*&
  [_]Client.s3 |-> ?_s3 &*&
  Client.l1 |-> _;

@*/

class Thread1 implements Runnable {

  public void run()
  //@ requires Runnable_pre(Thread1.class)(this, currentThread);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ open Runnable_pre(Thread1.class)(this, currentThread);
    Client.thread1();
  }
  
}

/*@

predicate_family_instance Runnable_pre(Thread2.class)(Thread2 thread2, int threadId) =
  [_]Client.s3 |-> ?_s3 &*&
  [_]atomic_space_({1}, Client_inv) &*&
  Client.l21 |-> _ &*&
  Client.l22_created |-> false &*&
  Client.l22 |-> _ &*&
  [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
  [_]Client.done |-> ?_done &*& _done != null &*&
  obs(threadId, ?p, {}) &*&
  call_below_perm(p, Program.class);

@*/

class Thread2 implements Runnable {

  public void run()
  //@ requires Runnable_pre(Thread2.class)(this, currentThread);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ open Runnable_pre(Thread2.class)(this, currentThread);
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Client.class);
    Client.thread2();
  }
  
}

class Program {

  public static void main(String[] args)
  //@ requires obs(currentThread, {}, {}) &*& class_init_token(Client.class);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Thread1.class);
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Thread2.class);
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    Client.main();
  }
  
}