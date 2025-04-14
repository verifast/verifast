// tab_size:2

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2025

/*@

fixpoint level L(int k) { return level(Client.class, {1 + Ticketlock_level_nb_dims, k}); }

predicate Client_inv() =
  [_]Client.lk |-> ?_lk &*& _lk.state(?owner, ?held) &*& Client_inv_(owner, held);
  
predicate done_value(long d) = true;

predicate Client_inv_(int owner, boolean held) =
  [_]Client.done |-> ?_done &*& done_value(?done) &*&
  [_]Client.ownerSignalsBox |-> ?ownerSignalsBox &*& growing_list<void *>(ownerSignalsBox, ?ownerSignals) &*&
  (
		!held ?
		  length(ownerSignals) == owner &*&
		  Client.leftThreadOwns |-> none
		:
		  [1/2]Client.leftThreadOwns |-> some(?leftThreadOwns) &*&
		  length(ownerSignals) == owner + 1 &*&
		  signal(nth(owner, ownerSignals), L(0), false)
  ) &*&
  (
    done == 0 ?
      [1/2]_done.state(0) &*& [_]Client.doneSignal |-> ?doneSignal &*& signal(doneSignal, L(2), false)
    :
      done == 1 &*& [_]_done.state(1)
  );

predicate seen_done_set(boolean b) = true;

@*/

class Client {

  static Ticketlock lk;
  static AtomicLong done;
  
  //@ static void *doneSignal;
  //@ static box ownerSignalsBox;
  //@ static option<boolean> leftThreadOwns;
  
  static void thread1()
  /*@
  requires
    [_]Client.doneSignal |-> ?doneSignal &*&
    obs(currentThread, ?p, {pair(doneSignal, L(2))}) &*&
    [_]atomic_space_({1}, Client_inv) &*&
    [_]lk |-> ?_lk &*& [_]_lk.valid({0}, L(1)) &*&
    [_]Client.ownerSignalsBox |-> ?ownerSignalsBox &*&
    [_]Client.done |-> ?_done &*& _done != null &*& [1/2]_done.state(0);
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    // create_wait_perm(, L(0), Ticketlock.class);
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    {
      /*@
      predicate waitInv(int oldOwner) =
				[_]atomic_space_({1}, Client_inv) &*&
				[_]lk |-> _lk &*& [_]_lk.valid({0}, L(1)) &*&
				[_]Client.ownerSignalsBox |-> ownerSignalsBox &*&
        [_]Client.done |-> _done &*&
        oldOwner == -1 ?
            true
        :
            exists(?ownerSignalHandle) &*& has_at(ownerSignalHandle, ownerSignalsBox, oldOwner, ?oldOwnerSignal) &*&
            wait_perm(p, oldOwnerSignal, L(0), Ticketlock_targetClass);
      predicate post(int owner) =
        [1/2]Client.leftThreadOwns |-> some(true) &*&
        has_at<void *>(_, ownerSignalsBox, owner, ?ownerSignal) &*&
        obs(currentThread, p, {pair(ownerSignal, L(0)), pair(doneSignal, L(2))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_wait_ghost_op(p, _lk, {0}, L(1), 1, waitInv, currentThread)(owner, newRound, op) {
        assert obs(_, _, ?obs);
        open waitInv(?oldOwner);
        assert atomic_spaces(?spaces);
        if (mem(pair({1}, Client_inv), spaces)) {
          mem_map(pair({1}, Client_inv), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
          assert false;
        }
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        op();
        open Client_inv_(_, true);
        is_ancestor_of_refl(p);
        assert growing_list(ownerSignalsBox, ?ownerSignals);
        if (newRound) {
            if (oldOwner != -1)
                open exists(_);
            open cp_lex(_, _, _);
            call_below_perm_lex_weaken({0});
            create_wait_perm(nth(owner, ownerSignals), L(0), Ticketlock_targetClass);
            handle newHandle = create_has_at(ownerSignalsBox, owner);
            close exists(newHandle);
        } else {
            match_has_at(ownerSignalsBox);
        }
        if (!forall(map(snd, obs), (level_lt)(L(0)))) {
            level badLevel = not_forall(map(snd, obs), (level_lt)(L(0)));
            forall_elim(map(snd, obs), (level_lt)(L(1)), badLevel);
            level_lt_trans(L(0), L(1), badLevel);
            assert false;
        }
        wait(nth(owner, ownerSignals));
        close Client_inv_(owner, true);
        close Client_inv();
        close_atomic_space({1}, Client_inv); 
        close waitInv(owner);
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(p, {pair(doneSignal, L(2))}, _lk, {0}, waitInv, post, currentThread)(owner, op) {
        open waitInv(_);
        assert atomic_spaces(?spaces);
        if (mem(pair({1}, Client_inv), spaces)) {
          mem_map(pair({1}, Client_inv), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
          assert false;
        }
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        op();
        open Client_inv_(_, false);
        is_ancestor_of_refl(p);
        Client.leftThreadOwns = some(true);
        void *ownerSignal = create_signal();
        init_signal(ownerSignal, L(0));
        growing_list_add(ownerSignalsBox, ownerSignal);
        create_has_at(ownerSignalsBox, owner);
        close Client_inv_(owner, true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post(owner);
      };
      @*/
      //@ close waitInv(-1);
      //@ produce_call_below_perm_();
      //@ call_below_perm__weaken(Ticketlock.class);
      lk.acquire();
      //@ open post(?owner);
    }
    //@ assert has_at(?ownerSignalHandle, ownerSignalsBox, ?owner, ?ownerSignal);
    {
      /*@
      predicate pre() =
        [_]Client.doneSignal |-> doneSignal &*&
        [_]Client.done |-> _done &*& [1/2]_done.state(0) &*&
        obs(currentThread, p, {pair(ownerSignal, L(0)), pair(doneSignal, L(2))}) &*&
        [_]atomic_space_({1}, Client_inv);
      predicate post() =
        obs(currentThread, p, {pair(ownerSignal, L(0))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_set_ghost_op(_done, 1, pre, post)(op) {
        open pre();
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        open Client_inv_(?owner1, ?held);
        open done_value(_);
        op();
        set_signal(doneSignal);
        close done_value(1);
        close Client_inv_(owner1, held);
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
        obs(currentThread, p, {pair(ownerSignal, L(0))}) &*&
        [1/2]Client.leftThreadOwns |-> some(true) &*&
        [_]Client.lk |-> _lk &*&
        [_]Client.ownerSignalsBox |-> ownerSignalsBox &*& has_at(ownerSignalHandle, ownerSignalsBox, owner, ownerSignal) &*&
        [_]atomic_space_({1}, Client_inv);
      predicate post(list<pathcomp> _p, list<pair<void *, level> > obs) =
        _p == p &*& obs == {};
      @*/
      /*@
      produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(_lk, {0}, L(1), owner, pre, post, currentThread)(op) {
        open pre();
        assert atomic_spaces(?spaces);
        if (mem(pair({1}, Client_inv), spaces)) {
          mem_map(pair({1}, Client_inv), spaces, fst);
          forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
          assert false;
        }
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        op();
        open Client_inv_(_, true);
        Client.leftThreadOwns = none;
        match_has_at(ownerSignalsBox);
        set_signal(ownerSignal);
        close Client_inv_(owner + 1, false);
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
    [_]atomic_space_({1}, Client_inv) &*&
    [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(1)) &*&
    [_]Client.done |-> ?_done &*& _done != null &*&
    [_]Client.doneSignal |-> ?doneSignal &*&
    obs(currentThread, ?p, {}) &*&
    [_]Client.ownerSignalsBox |-> ?ownerSignalsBox &*&
    call_below_perm(p, Program.class) &*&
    call_perm_(currentThread, Client.class);
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ create_wait_perm(doneSignal, L(2), Client.class);
    //@ close seen_done_set(false);
    for (;;)
    /*@
    invariant
      [_]Client.lk |-> _lk &*& [_]_lk.valid({0}, L(1)) &*&
      [_]Client.done |-> _done &*&
      [_]Client.doneSignal |-> doneSignal &*& wait_perm(p, doneSignal, L(2), Client.class) &*&
      obs(currentThread, p, {}) &*&
      [_]Client.ownerSignalsBox |-> ownerSignalsBox &*&
      [_]atomic_space_({1}, Client_inv) &*&
      seen_done_set(?seenDoneSet) &*&
      (
        !seenDoneSet ?
          call_perm_(currentThread, Client.class)
        :
          [_]_done.state(1)
      );
    @*/
    {
      {
        /*@
        predicate waitInv(int oldOwner) =
          [_]atomic_space_({1}, Client_inv) &*&
          [_]Client.lk |-> _lk &*&
    		  [_]Client.done |-> _done &*&
          [_]atomic_space_({1}, Client_inv) &*&
          [_]Client.ownerSignalsBox |-> ownerSignalsBox &*&
          oldOwner == -1 ?
            true
          :
            exists(?ownerSignalHandle) &*&
            has_at(ownerSignalHandle, ownerSignalsBox, oldOwner, ?oldOwnerSignal) &*&
            wait_perm(p, oldOwnerSignal, L(0), Ticketlock_targetClass);
        predicate post(int owner) =
          [1/2]leftThreadOwns |-> some(false) &*&
          has_at<void *>(_, ownerSignalsBox, owner, ?ownerSignal) &*&
          obs(currentThread, p, {pair(ownerSignal, L(0))});
        @*/
        /*@
        produce_lemma_function_pointer_chunk Ticketlock_wait_ghost_op(p, _lk, {0}, L(1), 1, waitInv, currentThread)(owner, newRound, op) {
          assert obs(_, _, ?obs);
		      open waitInv(?oldOwner);
		      assert atomic_spaces(?spaces);
		      if (mem(pair({1}, Client_inv), spaces)) {
		        mem_map(pair({1}, Client_inv), spaces, fst);
		        forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
		        assert false;
		      }
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      op();
          open Client_inv_(owner, true);
          assert growing_list(ownerSignalsBox, ?ownerSignals);
          if (newRound) {
            if (oldOwner != -1) {
              open exists(_);
            }
            open cp_lex(_, _, _);
            call_below_perm_lex_weaken({0});
            create_wait_perm(nth(owner, ownerSignals), L(0), Ticketlock_targetClass);
            handle newOwnerSignalHandle = create_has_at(ownerSignalsBox, owner);
            close exists(newOwnerSignalHandle);
          } else {
            match_has_at(ownerSignalsBox);
          }
          assert done_value(?d);
          is_ancestor_of_refl(p);
          if (!forall(map(snd, obs), (level_lt)(L(0)))) {
              level badLevel = not_forall(map(snd, obs), (level_lt)(L(0)));
              forall_elim(map(snd, obs), (level_lt)(L(1)), badLevel);
              level_lt_trans(L(0), L(1), badLevel);
              assert false;
          }
          wait(nth(owner, ownerSignals));
          close Client_inv_(owner, true);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close waitInv(owner);
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(p, {}, _lk, {0}, waitInv, post, currentThread)(owner, op) {
		      open waitInv(?oldOwner);
		      assert atomic_spaces(?spaces);
		      if (mem(pair({1}, Client_inv), spaces)) {
		        mem_map(pair({1}, Client_inv), spaces, fst);
		        forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
		        assert false;
		      }
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      op();
          open Client_inv_(owner, false);
          assert growing_list(ownerSignalsBox, ?ownerSignals);
          Client.leftThreadOwns = some(false);
          assert done_value(?d);
          void *ownerSignal = create_signal();
          init_signal(ownerSignal, L(0));
          growing_list_add(ownerSignalsBox, ownerSignal);
          create_has_at(ownerSignalsBox, owner);
          close Client_inv_(owner, true);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close post(owner);
        };
        @*/
        //@ produce_call_below_perm_();
        //@ call_below_perm__weaken(Ticketlock.class);
        //@ close waitInv(-1);
        lk.acquire();
        //@ open post(_);
      }
      //@ assert has_at(_, _, ?owner, ?ownerSignal);
      long value;
      {
        /*@
        predicate pre() =
          [_]Client.done |-> _done &*&
          (!seenDoneSet ? true : [_]_done.state(1)) &*&
          [_]atomic_space_({1}, Client_inv);
        predicate post(long result) =
          result == 0 ?
            !seenDoneSet
          :
            [_]_done.state(1);
        @*/
        /*@
        produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(_done, pre, post)(op) {
          open pre();
          open_atomic_space({1}, Client_inv);
          open Client_inv();
          open Client_inv_(?owner_, ?held);
          assert [_]_done.state(?d);
          op();
          close Client_inv_(owner_, held);
          close Client_inv();
          close_atomic_space({1}, Client_inv);
          close post(d);
        };
        @*/
        //@ close pre();
        value = done.get();
        //@ open post(_);
      }
      //@ open seen_done_set(seenDoneSet);
      {
        /*@
        predicate pre() =
          [_]Client.doneSignal |-> doneSignal &*& wait_perm(p, doneSignal, L(2), Client.class) &*&
          obs(currentThread, p, {pair(ownerSignal, L(0))}) &*&
          [_]Client.ownerSignalsBox |-> ownerSignalsBox &*&
          has_at(_, ownerSignalsBox, owner, ownerSignal) &*&
          [1/2]Client.leftThreadOwns |-> some(false) &*&
          [_]Client.lk |-> _lk &*& [_]Client.done |-> _done &*& (!seenDoneSet ? true : [_]_done.state(1)) &*&
          [_]atomic_space_({1}, Client_inv);
        predicate post(list<pathcomp> _p, list<pair<void *, level> > obs) =
          wait_perm(p, doneSignal, L(2), Client.class) &*&
          seen_done_set(?seenDoneSet1) &*&
          (
            !seenDoneSet1 ?
              !seenDoneSet &*&
              call_perm_(currentThread, Client.class)
            :
              [_]_done.state(1)
          ) &*&
          _p == p &*& obs == {};
        @*/
        /*@
        produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(_lk, {0}, L(1), owner, pre, post, currentThread)(op) {
		      open pre();
		      assert atomic_spaces(?spaces);
		      if (mem(pair({1}, Client_inv), spaces)) {
		        mem_map(pair({1}, Client_inv), spaces, fst);
		        forall_elim(map(fst, spaces), (is_prefix_of)({0}), {1});
		        assert false;
		      }
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      op();
          open Client_inv_(owner, true);
          Client.leftThreadOwns = none;
          assert growing_list(ownerSignalsBox, ?ownerSignals);
          match_has_at(ownerSignalsBox);
          set_signal(nth(owner, ownerSignals));
        	assert done_value(?d);
        	if (d == 0) {
        	  is_ancestor_of_refl(p);
        	  wait(doneSignal);
        	}
        	close seen_done_set(d != 0);
          close Client_inv_(owner + 1, false);
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

  static void main()
  /*@
  requires
    obs(currentThread, {}, {}) &*&
    class_init_token(Client.class) &*&
    call_perm_(currentThread, Client.class) &*&
    call_perm_(currentThread, Thread1.class) &*&
    call_below_perm({}, Program.class);
  @*/
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ init_class(Client.class);
    //@ close exists(pair({0}, L(1)));
    lk = new Ticketlock();
    //@ leak Client.lk |-> _;
    done = new AtomicLong();
    //@ leak Client.done |-> _;
    //@ void *doneSignal = create_signal();
    //@ init_signal(doneSignal, L(2));
    //@ Client.doneSignal = doneSignal;
    //@ leak Client.doneSignal |-> _;
    //@ close done_value(0);
    //@ Client.leftThreadOwns = none;
    //@ box ownerSignalsBox = create_growing_list();
    //@ Client.ownerSignalsBox = ownerSignalsBox;
    //@ leak Client.ownerSignalsBox |-> ownerSignalsBox;
    //@ close Client_inv_(0, false);
    //@ close Client_inv();
    //@ create_atomic_space_({1}, Client_inv);
    //@ leak atomic_space_({1}, Client_inv);
    
    Thread1 thread1 = new Thread1();
    {
      /*@
      predicate pre() =
				[_]atomic_space_({1}, Client_inv) &*&
				[_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(1)) &*&
				[_]Client.done |-> ?_done &*& _done != null &*& [1/2]_done.state(0) &*&
				[_]Client.ownerSignalsBox |-> _ &*&
				[_]Client.doneSignal |-> doneSignal;
      predicate post() = obs(currentThread, {Forker}, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {}, {pair(doneSignal, L(2))}, {}, thread1, pre, post)(forkeeId) {
        open pre();
        close post();
        close Runnable_pre(Thread1.class)(thread1, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(thread1).start();
      //@ open post();
    }
    
    //@ call_below_perm_weaken_path({Forker});
    thread2();
  }
  
}

/*@

predicate_family_instance Runnable_pre(Thread1.class)(Thread1 thread1, int threadId) =
  [_]Client.doneSignal |-> ?doneSignal &*&
  [_]Client.ownerSignalsBox |-> _ &*&
  obs(threadId, ?p, {pair(doneSignal, L(2))}) &*&
  [_]atomic_space_({1}, Client_inv) &*&
  [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(1)) &*&
  [_]Client.done |-> ?_done &*& _done != null &*& [1/2]_done.state(0);

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

class Program {

  public static void main(String[] args)
  //@ requires obs(currentThread, {}, {}) &*& class_init_token(Client.class);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Thread1.class);
    //@ produce_call_below_perm_();
    //@ call_below_perm__to_call_perm_(Client.class);
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    Client.main();
  }
  
}
