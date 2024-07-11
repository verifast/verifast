// tab_size:2

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

fixpoint level L(int k) { return level(Client.class, {1 + Spinlock_level_nb_dims, k}); }

predicate grabbed(boolean b) = true;

predicate Client_inv() =
  [_]Client.lk |-> ?_lk &*& _lk.state(?b) &*& Client_inv_(b);
  
predicate Client_inv_(boolean b) =
  [_]Client.f |-> ?_f &*& [1/2]_f.state(?d) &*&
  [_]Client.middleThread |-> pair(?_middleThread, ?_middlePhase) &*&
  (
    !b ?
      Client.lockOwner |-> none
    :
      [1/2]Client.lockOwner |-> some(?leftThreadOwns) &*&
      leftThreadOwns ?
        d == 1 ?
          [_]Client.l11 |-> ?_l11 &*& signal(_l11, L(0), false)
        :
          [_]Client.l12 |-> ?_l12 &*& signal(_l12, L(0), false)
      :
        [_]Client.l2 |-> ?_l2 &*& signal(_l2, L(0), false)
  ) &*&
  d == 1 ?
    [_]Client.sf |-> ?_sf &*& signal(_sf, L(1), false) &*&
    hidden_obs(_middleThread, _middlePhase, {})
  :
    d == 0 &*&
    [_]_f.state(0) &*&
    grabbed(?_grabbed) &*&
    !_grabbed ?
      [_]Client.l12 |-> ?_l12 &*&
      hidden_obs(_middleThread, _middlePhase, {pair(_l12, L(0))}) &*&
      [_]Client.lk |-> ?_lk &*& _lk.held() &*&
      [1/2]Client.lockOwner |-> some(true)
    :
      Client.ho |-> _;

predicate started(boolean b) = true;

predicate waiting_for_l11(boolean b) = true;

predicate hidden_obs(int threadId, list<pathcomp> phase, list<pair<void *, level> > obs) = obs(threadId, phase, obs);

predicate hidden_f_state(AtomicLong f, long value) = f.state(value);

@*/

class Client {
  
  static Spinlock lk;
  static AtomicLong f;
  
  //@ static pair<int, list<pathcomp> > middleThread;
  
  //@ static void *sf = default_value;
  //@ static void *l11 = default_value;
  //@ static void *l12 = default_value;
  //@ static void *l2 = default_value;
  
  //@ static option<boolean> lockOwner; // none = no owner; some(true) = left thread; some(false) = right thread
  //@ static unit ho;

  static void thread1()
  /*@
  requires
      [_]Client.sf |-> ?_sf &*&
      Client.l11 |-> _ &*&
      Client.l12 |-> _ &*&
      obs(currentThread, ?p, {pair(_sf, L(1))}) &*&
      [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
      [_]Client.f |-> ?_f &*& [1/2]_f.state(1) &*&
      [_]atomic_space_({1}, Client_inv);
  @*/
  //@ ensures obs(currentThread, p, {});
  //@ terminates;
  {
    //@ int callerThread = currentThread;
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    {
      /*@
      predicate waitInv() =
        [_]Client.lk |-> _lk &*&
        Client.l11 |-> _ &*&
        Client.l12 |-> _ &*&
        [_]Client.f |-> _f &*& [1/2]_f.state(1) &*&
        [_]atomic_space_({1}, Client_inv) &*&
        started(?started_) &*&
        !started_ ?
          call_below_perm(p, Client.class)
        :
          [_]l2 |-> ?_l2 &*& wait_perm(p, _l2, L(0), Spinlock.class)
        ;
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        [_]Client.lk |-> _lk &*&
        Client.l11 |-> _ &*&
        Client.l12 |-> _ &*&
        [_]Client.f |-> _f &*& [1/2]_f.state(1) &*&
        [_]atomic_space_({1}, Client_inv) &*&
        atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*&
        Client_inv_(held) &*&
        started(?started_) &*&
        !started_ ?
          call_below_perm(p, Client.class)
        :
          [_]l2 |-> ?_l2 &*& wait_perm(p, _l2, L(0), Spinlock.class)
        ;
      predicate post() =
        Client.l12 |-> _ &*&
        [_]Client.f |-> _f &*& [1/2]_f.state(1) &*&
        [_]Client.l11 |-> ?_l11 &*& obs(currentThread, p, {pair(_l11, L(0)), pair(_sf, L(1))}) &*& [1/2]Client.lockOwner |-> some(true);
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
        assert _lk.state(?held);
        close R(spaces, held);
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_wait_ghost_op(_lk, R, currentThread, p, L(0), waitInv)() {
        assert obs(callerThread, p, ?obs);
        open R(?spaces, true);
        open Client_inv_(true);
        assert [_]Client.lockOwner |-> some(?leftThreadOwns);
        assert [_]Client.l2 |-> ?_l2;
        assert started(?started_);
        if (!started_) {
          create_wait_perm(_l2, L(0), Spinlock.class);
          open started(false);
          close started(true);
        }
        is_ancestor_of_refl(p);
        wait(_l2);
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close waitInv();
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_acquire_ghost_op(_lk, R, p, {pair(_sf, L(1))}, post, currentThread)() {
        open R(?spaces, false);
        open Client_inv_(false);
        Client.lockOwner = some(true);
        void *l11 = create_signal();
        init_signal(l11, L(0));
        Client.l11 = l11;
        leak Client.l11 |-> l11;
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close started(false);
      //@ close waitInv();
      lk.acquire();
      //@ open post();
    }
    {
      /*@
      predicate pre() =
        [_]atomic_space_({1}, Client_inv) &*&
        [_]Client.f |-> _f &*& [1/2]_f.state(1) &*&
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.lk |-> _lk &*& _lk.held() &*&
        [_]Client.l11 |-> ?_l11 &*&
        Client.l12 |-> _ &*&
        [_]Client.sf |-> _sf &*&
        obs(currentThread, p, {pair(_l11, L(0)), pair(_sf, L(1))});
      predicate post() =
        obs(currentThread, p, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk AtomicLong_set_ghost_op(_f, 0, pre, post)(op) {
        open pre();
        open_atomic_space({1}, Client_inv);
        open Client_inv();
        open Client_inv_(?held);
        op();
        set_signal(Client.l11);
        set_signal(Client.sf);
        close hidden_obs(callerThread, p, {});
        assert [_]Client.middleThread |-> pair(?_middleThread, ?_middlePhase);
        open hidden_obs(_middleThread, _middlePhase, {});
        void *l12 = create_signal();
        Client.l12 = l12;
        leak Client.l12 |-> l12;
        init_signal(l12, L(0));
        close hidden_obs(_middleThread, _middlePhase, _);
        open hidden_obs(callerThread, _, _);
        close grabbed(false);
        close Client_inv_(held);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close pre();
      f.set(0);
      //@ open post();
    }
  }

  static void thread2()
  /*@
  requires
    [_]Client.sf |-> ?_sf &*&
    [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
    [_]Client.f |-> ?_f &*& _f != null &*&
    [_]atomic_space_({1}, Client_inv) &*&
    [_]Client.middleThread |-> pair(currentThread, ?p) &*&
    call_below_perm(p, Program.class) &*&
    Client.ho |-> _;
  @*/
  //@ ensures obs(currentThread, p, {});
  //@ terminates;
  {
    //@ int callerThread = currentThread;
    //@ create_wait_perm(_sf, L(1), Client.class);
    for (;;)
    /*@
    invariant
      [_]Client.sf |-> _sf &*& wait_perm(p, _sf, L(1), Client.class) &*&
      [_]Client.lk |-> _lk &*& [_]_lk.valid({0}, L(0)) &*&
      [_]Client.f |-> _f &*& _f != null &*&
      [_]atomic_space_({1}, Client_inv) &*&
      [_]Client.middleThread |-> pair(currentThread, p) &*&
      Client.ho |-> _;
    @*/
    {
      long v;
      {
		    /*@
		    predicate pre() =
		      [_]Client.sf |-> _sf &*& wait_perm(p, _sf, L(1), Client.class) &*&
		      [_]Client.lk |-> _lk &*&
		      [_]Client.f |-> _f &*& _f != null &*&
		      [_]atomic_space_({1}, Client_inv) &*&
		      [_]Client.middleThread |-> pair(currentThread, p) &*&
		      Client.ho |-> _;
		    predicate post(long value) =
		      wait_perm(p, _sf, L(1), Client.class) &*&
		      value != 0 ?
   		      Client.ho |-> _ &*&
		        call_perm_(currentThread, Client.class)
		      :
		        [_]_f.state(0) &*&
		        [_]Client.l12 |-> ?_l12 &*&
		        obs(currentThread, p, {pair(_l12, L(0))}) &*&
		        [1/2]Client.lockOwner |-> some(true) &*& _lk.held();
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk AtomicLong_get_ghost_op(_f, pre, post)(op) {
		      open pre();
		      open_atomic_space({1}, Client_inv);
		      open Client_inv();
		      open Client_inv_(?held);
		      assert [_]_f.state(?value);
		      op();
		      if (value == 1) {
		        open hidden_obs(callerThread, p, {});
		        is_ancestor_of_refl(p);
		        wait(_sf);
		        close hidden_obs(callerThread, p, {});
		      } else {
		        open grabbed(false);
		        close grabbed(true);
		        open hidden_obs(callerThread, p, _);
		        close [1/2]hidden_f_state(_f, 0);
		        assert [?f]_f.state(0);
		        close [f/2]hidden_f_state(_f, 0);
		        open [1/2]hidden_f_state(_f, 0);
		      }
		      close Client_inv_(held);
		      close Client_inv();
		      close_atomic_space({1}, Client_inv);
		      if (value != 1)
  		      open hidden_f_state(_f, 0);
		      close post(value);
		    };
		    @*/
		    //@ close pre();
		    v = f.get();
		    //@ open post(v);
		  }
		  if (v == 0)
		    break;
		}
    //@ assert [_]Client.l12 |-> ?_l12;
    {
      /*@
      predicate pre() =
        [_]Client.f |-> _f &*&
        [_]_f.state(0) &*&
        [_]Client.lk |-> _lk &*&
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.l12 |-> _l12 &*&
        obs(currentThread, p, {pair(_l12, L(0))}) &*&
        [_]atomic_space_({1}, Client_inv);
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        [_]Client.f |-> _f &*&
        [_]_f.state(0) &*&
        [_]Client.lk |-> _lk &*&
        [1/2]Client.lockOwner |-> some(true) &*&
        [_]Client.l12 |-> _l12 &*&
        obs(currentThread, p, {pair(_l12, L(0))}) &*&
        Client_inv_(held) &*& atomic_spaces(cons(pair({1}, Client_inv), spaces));
      predicate post(list<pathcomp> _p, list<pair<void *, level> > _obs) =
        _p == p &*& _obs == {};
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
        close Client_inv_(false);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        set_signal(_l12);
        close post(p, {});
      };
      @*/
      //@ close pre();
      lk.release();
      //@ open post(_, _);
    }
  }

  static void thread3()
  /*@
  requires
    [_]Client.f |-> ?_f &*&
    [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
    [_]atomic_space_({1}, Client_inv) &*&
    Client.l2 |-> _ &*&
    obs(currentThread, ?p, {});
  @*/
  //@ ensures obs(currentThread, p, {});
  //@ terminates;
  {
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ merge_fractions call_below_perm(p, Client.class);
    {
      /*@
      predicate waitInv() =
        [_]Client.f |-> _f &*&
        [_]Client.lk |-> _lk &*&
        Client.l2 |-> _ &*&
        [_]atomic_space_({1}, Client_inv) &*&
        started(?_started) &*&
        _started ?
          waiting_for_l11(?waitingForL11) &*&
          waitingForL11 ?
            [_]Client.l11 |-> ?_l11 &*& wait_perm(p, _l11, L(0), Spinlock.class) &*& call_below_perm(p, Client.class)
          :
            [_]_f.state(0) &*&
            [_]Client.l12 |-> ?_l12 &*& wait_perm(p, _l12, L(0), Spinlock.class)
        :
          [2]call_below_perm(p, Client.class);
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        [_]Client.f |-> _f &*&
        [_]atomic_space_({1}, Client_inv) &*&
        [_]Client.lk |-> _lk &*&
        Client.l2 |-> _ &*&
        atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*&
        Client_inv_(held) &*&
        started(?_started) &*&
        _started ?
          waiting_for_l11(?waitingForL11) &*&
          waitingForL11 ?
            [_]Client.l11 |-> ?_l11 &*& wait_perm(p, _l11, L(0), Spinlock.class) &*& call_below_perm(p, Client.class)
          :
            [_]_f.state(0) &*&
            [_]Client.l12 |-> ?_l12 &*& wait_perm(p, _l12, L(0), Spinlock.class)
        :
          [2]call_below_perm(p, Client.class);
      predicate post() =
        [_]Client.l2 |-> ?_l2 &*&
        [1/2]Client.lockOwner |-> some(false) &*&
        obs(currentThread, p, {pair(_l2, L(0))});
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
        is_ancestor_of_refl(p);
        assert [_]_f.state(?d);
        assert started(?_started);
        boolean saved_f_state = false;
        if (d == 1) {
          void *_l11 = Client.l11;
          if (!_started) {
            create_wait_perm(_l11, L(0), Spinlock.class);
            open started(false);
            close started(true);
            close waiting_for_l11(true);
          }
          wait(_l11);
        } else {
          assert [?frac]_f.state(0);
          close [(frac - 1/2)/2]hidden_f_state(_f, 0);
          saved_f_state = true;
          void *_l12 = Client.l12;
          if (!_started) {
            create_wait_perm(_l12, L(0), Spinlock.class);
            open started(false);
            close started(true);
            close waiting_for_l11(false);
          } else {
            assert waiting_for_l11(?waitingForL11);
            if (waitingForL11) {
              create_wait_perm(_l12, L(0), Spinlock.class);
              open waiting_for_l11(true);
              close waiting_for_l11(false);
            }
          }
          wait(_l12);
        }
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        if (saved_f_state)
          open hidden_f_state(_f, 0);
        close waitInv();
      };
      @*/
      /*@
      produce_lemma_function_pointer_chunk Spinlock_acquire_ghost_op(_lk, R, p, {}, post, currentThread)() {
        open R(?spaces, false);
        open Client_inv_(false);
        Client.lockOwner = some(false);
        void *l2 = create_signal();
        init_signal(l2, L(0));
        Client.l2 = l2;
        leak Client.l2 |-> l2;
        close Client_inv_(true);
        close Client_inv();
        close_atomic_space({1}, Client_inv);
        close post();
      };
      @*/
      //@ close started(false);
      //@ close waitInv();
      lk.acquire();
      //@ open post();
    }
    //@ void *_l2 = Client.l2;
    {
      /*@
      predicate pre() =
        [_]atomic_space_({1}, Client_inv) &*&
        [_]Client.lk |-> _lk &*&
        [_]Client.l2 |-> _l2 &*&
        [1/2]Client.lockOwner |-> some(false) &*&
        obs(currentThread, p, {pair(_l2, L(0))});
      predicate R(list<pair<list<int>, predicate()> > spaces, boolean held) =
        [_]Client.lk |-> _lk &*&
        [1/2]Client.lockOwner |-> some(false) &*&
        [_]Client.l2 |-> _l2 &*&
        obs(currentThread, p, {pair(_l2, L(0))}) &*&
        atomic_spaces(cons(pair({1}, Client_inv), spaces)) &*&
        Client_inv_(held);
      predicate post(list<pathcomp> _p, list<pair<void *, level> > _obs) =
        _p == p &*& _obs == {};
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
        set_signal(_l2);
        Client.lockOwner = none;
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

  public static void main()
  //@ requires obs(currentThread, {}, {}) &*& class_init_token(Client.class) &*& call_perm_(currentThread, Thread1.class) &*& call_perm_(currentThread, Thread2.class) &*& call_below_perm({}, Program.class);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ init_class(Client.class);
    
    //@ close exists(pair({0}, L(0)));
    lk = new Spinlock();
    //@ leak Client.lk |-> _;
    f = new AtomicLong(1);
    //@ leak Client.f |-> _;
    //@ Client.lockOwner = none;
    //@ void *_sf = create_signal();
    //@ init_signal(_sf, L(1));
    //@ Client.sf = _sf;
    //@ leak Client.sf |-> _sf;
    Thread2 thread2 = new Thread2();
    {
      /*@
      predicate pre() =
        [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*& _lk.state(false) &*&
        [_]Client.f |-> ?_f &*& [1/2]_f.state(1) &*&
        Client.lockOwner |-> none &*&
        [_]Client.sf |-> _sf &*& signal(_sf, L(1), false) &*&
        Client.middleThread |-> _ &*&
        call_below_perm({}, Program.class) &*&
        Client.ho |-> _;
      predicate post() =
        [_]Client.middleThread |-> _ &*&
        [_]atomic_space_({1}, Client_inv) &*&
        obs(currentThread, {Forker}, {pair(_sf, L(1))});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {}, {pair(_sf, L(1))}, {pair(_sf, L(1))}, thread2, pre, post)(forkeeId) {
        open pre();
        Client.middleThread = pair(forkeeId, {Forkee});
        leak Client.middleThread |-> _;
        close hidden_obs(forkeeId, {Forkee}, {});
        close Client_inv_(false);
        close Client_inv();
        create_atomic_space_({1}, Client_inv);
        leak atomic_space_({1}, Client_inv);
        close post();
        close Runnable_pre(Thread2.class)(thread2, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(thread2).start();
      //@ open post();
    }
    Runnable thread1 = new Thread1();
    {
      /*@
      predicate pre() =
        [_]Client.sf |-> _sf &*&
        Client.l11 |-> _ &*&
        Client.l12 |-> _ &*&
        [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
        [_]Client.f |-> ?_f &*& [1/2]_f.state(1) &*&
        [_]atomic_space_({1}, Client_inv);
      predicate post() =
        obs(currentThread, {Forker, Forker}, {});
      @*/
      /*@
      produce_lemma_function_pointer_chunk Thread_start_ghost_op(currentThread, {Forker}, {pair(_sf, L(1))}, {}, thread1, pre, post)(forkeeId) {
        open pre();
        close post();
        close Runnable_pre(Thread1.class)(thread1, forkeeId);
      };
      @*/
      //@ close pre();
      new Thread(thread1).start();
      //@ open post();
    }
    thread3();
  }

}

/*@

predicate_family_instance Runnable_pre(Thread1)(Runnable this, int threadId) =
  [_]Client.sf |-> ?_sf &*&
  obs(threadId, _, {pair(_sf, L(1))}) &*&
  Client.l11 |-> _ &*&
  Client.l12 |-> _ &*&
  [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
  [_]Client.f |-> ?_f &*& [1/2]_f.state(1) &*&
  [_]atomic_space_({1}, Client_inv);

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

predicate_family_instance Runnable_pre(Thread2)(Runnable this, int threadId) =
  [_]Client.sf |-> ?_sf &*&
  [_]Client.lk |-> ?_lk &*& [_]_lk.valid({0}, L(0)) &*&
  [_]Client.f |-> ?_f &*& _f != null &*&
  [_]atomic_space_({1}, Client_inv) &*&
  [_]Client.middleThread |-> pair(threadId, ?p) &*&
  call_below_perm({}, Program.class) &*&
  Client.ho |-> _;



@*/

class Thread2 implements Runnable {

  public void run()
  //@ requires Runnable_pre(Thread2.class)(this, currentThread);
  //@ ensures obs(currentThread, _, {});
  //@ terminates;
  {
    //@ open Runnable_pre(Thread2.class)(this, currentThread);
    //@ assert [_]Client.middleThread |-> pair(_, ?p);
    //@ is_ancestor_of_nil(p);
    //@ call_below_perm_weaken_path(p);
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