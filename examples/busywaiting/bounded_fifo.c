// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

//@ #include <listex.gh>

//@ inductive pathcomp = Forker | Forkee;

/*@

fixpoint bool is_ancestor_of(list<pathcomp> p1, list<pathcomp> p2) {
  switch (p2) {
    case nil: return p1 == nil;
    case cons(p2h, p2t): return p1 == p2 || is_ancestor_of(p1, p2t);
  }
}

@*/

//@ predicate obs(list<pathcomp> path, list<pair<void *, int> > obs);

/*@

predicate call_below_perm(list<pathcomp> path, void *f;);

lemma void pathize_call_below_perm_();
  requires obs(?p, ?obs) &*& call_below_perm_(currentThread, ?f);
  ensures obs(p, obs) &*& call_below_perm(p, f);

fixpoint bool lt(int x, int y) { return x < y; }

@*/

struct mutex;
typedef struct mutex *mutex;

//@ predicate mutex(mutex mutex; int level, predicate() inv);
//@ predicate locked(mutex mutex, int level, predicate() inv, real frac);

mutex create_mutex();
//@ requires exists<int>(?level) &*& exists<predicate()>(?inv) &*& inv();
//@ ensures mutex(result, level, inv);
//@ terminates;

void acquire(mutex mutex);
//@ requires obs(?p, ?obs) &*& [?f]mutex(mutex, ?level, ?inv) &*& forall(map(snd, obs), (lt)(level)) == true;
//@ ensures obs(p, cons(pair(mutex, level), obs)) &*& locked(mutex, level, inv, f) &*& inv();
//@ terminates;

void release(mutex mutex);
//@ requires obs(?p, ?obs) &*& locked(mutex, ?level, ?inv, ?f) &*& inv();
//@ ensures obs(p, remove(pair(mutex, level), obs)) &*& [f]mutex(mutex, level, inv);
//@ terminates;

/*@

typedef lemma void release_ghost_op(int tid, list<pathcomp> p, list<pair<void *, int> > obs, predicate() inv, predicate() pre, predicate() post)();
  requires obs(p, obs) &*& pre() &*& currentThread == tid;
  ensures obs(p, obs) &*& inv() &*& post();

@*/

void release_with_ghost_op(mutex mutex);
//@ requires obs(?p, ?obs) &*& locked(mutex, ?level, ?inv, ?f) &*& is_release_ghost_op(_, currentThread, p, remove(pair(mutex, level), obs), inv, ?pre, ?post) &*& pre();
//@ ensures obs(p, remove(pair(mutex, level), obs)) &*& [f]mutex(mutex, level, inv) &*& post();
//@ terminates;

typedef void thread_run/*@(list<pathcomp> path, list<pair<void *, int> > obs, predicate() pre)@*/();
//@ requires obs(cons(Forkee, path), obs) &*& pre();
//@ ensures obs(_, nil);
//@ terminates;

void fork(thread_run *run);
//@ requires obs(?p, ?obs) &*& [_]is_thread_run(run, p, ?forkee_obs, ?pre) &*& pre();
//@ ensures obs(cons(Forker, p), remove_all(forkee_obs, obs));
//@ terminates;

/*@

predicate signal(void *id; int level, bool status);

lemma void *create_signal(int level);
  requires obs(?p, ?obs) &*& 0 <= level;
  ensures obs(p, cons(pair(result, level), obs)) &*& signal(result, level, false);

lemma void set_signal(void *signal);
  requires obs(?p, ?obs) &*& signal(signal, ?level, false);
  ensures obs(p, remove(pair(signal, level), obs)) &*& signal(signal, level, true);

predicate wait_perm(list<pathcomp> path, void *signal, int level, void *func;);

lemma void create_wait_perm(void *s, int level, void *f);
  requires call_below_perm(?p, ?f0) &*& func_lt(f, f0) == true;
  ensures wait_perm(p, s, level, f);

lemma void wait(void *s);
  requires
    obs(?p, ?obs) &*& wait_perm(?pp, s, ?level, ?f) &*&
    signal(s, level, false) &*&
    is_ancestor_of(pp, p) == true &*&
    forall(map(snd, obs), (lt)(level)) == true;
  ensures
    obs(p, obs) &*& wait_perm(pp, s, level, f) &*&
    signal(s, level, false) &*&
    call_perm_(currentThread, f);

@*/

mutex m;
int producerNext = 100;
int consumerNext = 100;

// TODO: Support global ghost variables. This is a workaround.
struct g {
  //@ void *produceSignal;
  //@ void *consumeSignal;
};
struct g g;

/*@

predicate call_below_perms(int count;) =
  count <= 0 ?
    true
  :
    call_below_perm({}, main) &*& call_below_perms(count - 1);

predicate mutex_inv(;) = mutex_inv_aux(_, _);

predicate mutex_inv_aux(; int cp, int cc) =
  [1/2]producerNext |-> cp &*&
  [1/2]consumerNext |-> cc &*&
  [1/2]g.produceSignal |-> ?sp &*&
  [1/2]g.consumeSignal |-> ?sc &*&
  0 <= cp &*& cp <= cc &*& cc <= 100 &*&
  call_below_perms(cp) &*&
  call_below_perms(cc - 11) &*&
  (
    cp == 0 ?
      true
    :
      signal(sp, 101 - cp, false) &*&
      wait_perm({}, sp, 101 - cp, consumer)
  ) &*&
  (
    cc <= 10 ?
      true
    :
      signal(sc, 102 - cc, false) &*&
      wait_perm({}, sc, 102 - cc, producer)
  );

@*/

void producer()
//@ requires [1/2]producerNext |-> 100 &*& [1/2]g.produceSignal |-> ?sp0 &*& obs({Forkee}, {pair(sp0, 1)}) &*& [_]m |-> ?mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
//@ ensures obs({Forkee}, {});
//@ terminates;
{
  for (;;)
  //@ invariant [1/2]producerNext |-> ?cp &*& [1/2]g.produceSignal |-> ?sp &*& 0 < cp &*& cp <= 100 &*& obs({Forkee}, {pair(sp, 101 - cp)}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
  //@ decreases cp; // For this loop, we don't consume call_perms
  {
    for (;;)
    //@ invariant [1/2]producerNext |-> cp &*& [1/2]g.produceSignal |-> sp &*& obs({Forkee}, {pair(sp, 101 - cp)}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
    {
      acquire(m);
      //@ open mutex_inv();
      //@ open mutex_inv_aux(_, ?cc);
      if (consumerNext - producerNext < 10) {
        //@ leak wait_perm({}, sp, 101 - cp, consumer);
        producerNext--;
        //@ set_signal(sp);
        //@ leak signal(sp, 101 - cp, true);
        if (producerNext == 0) {
          //@ close mutex_inv();
          release(m);
          //@ leak call_below_perms(_) &*& [1/2]g.produceSignal |-> _ &*& [1/2]producerNext |-> _ &*& [1/2]mutex(mutex, 0, mutex_inv);
          return;
        } else {
          //@ void *new_sp = create_signal(101 - producerNext);
          //@ g.produceSignal = new_sp;
          //@ open call_below_perms(cp);
          //@ create_wait_perm(new_sp, 101 - producerNext, consumer);
          //@ close mutex_inv_aux(cp - 1, cc);
          //@ close mutex_inv();
          release(m);
          break;
        }
      } else {
        /*@
        predicate pre() = mutex_inv_aux(cp, cc);
        predicate post() = call_perm_(currentThread, producer);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(currentThread, {Forkee}, {pair(sp, 101 - cp)}, mutex_inv, pre, post)() {
          open pre();
          wait(g.consumeSignal);
          close post();
        };
        @*/
        //@ close pre();
        release_with_ghost_op(m);
        //@ open post();
      }
    }
  }
}

void consumer()
//@ requires [1/2]consumerNext |-> 100 &*& [1/2]g.consumeSignal |-> ?sc0 &*& obs({Forker}, {pair(sc0, 2)}) &*& [_]m |-> ?mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
//@ ensures obs(_, {});
//@ terminates;
{
  for (;;)
  //@ invariant [1/2]consumerNext |-> ?cc &*& [1/2]g.consumeSignal |-> ?sc &*& 0 < cc &*& cc <= 100 &*& obs({Forker}, cc <= 10 ? {} : {pair(sc, 102 - cc)}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
  //@ decreases cc;
  {
    //@ assert obs(_, ?obs);
    for (;;)
    //@ invariant [1/2]consumerNext |-> cc &*& [1/2]g.consumeSignal |-> sc &*& obs({Forker}, obs) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
    {
      acquire(m);
      //@ open mutex_inv();
      //@ open mutex_inv_aux(?cp, _);
      if (producerNext < consumerNext) {
        /*@
        if (cc > 10) {
          leak wait_perm({}, sc, 102 - cc, producer);
          set_signal(sc);
          leak signal(sc, 102 - cc, true);
        }
        @*/
        consumerNext--;
        if (consumerNext == 0) {
          //@ close mutex_inv();
          release(m);
          //@ leak call_below_perms(_) &*& [1/2]g.consumeSignal |-> _ &*& [1/2]consumerNext |-> 0 &*& [1/2]mutex(mutex, 0, mutex_inv);
          return;
        } else {
          /*@
          {
            if (cc <= 11) {
              open call_below_perms(cc - 11);
              close call_below_perms(cc - 12);
            } else {
              void *new_sc = create_signal(102 - consumerNext);
              g.consumeSignal = new_sc;
              open call_below_perms(cc - 11);
              create_wait_perm(new_sc, 102 - consumerNext, producer);
            }
            close mutex_inv_aux(cp, cc - 1);
            close mutex_inv();
          }
          @*/
          release(m);
          break;
        }
      } else {
        /*@
        predicate pre() = mutex_inv_aux(cp, cc);
        predicate post() = call_perm_(currentThread, consumer);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(currentThread, {Forker}, obs, mutex_inv, pre, post)() {
          open pre();
          wait(g.produceSignal);
          close post();
        };
        @*/
        //@ close pre();
        release_with_ghost_op(m);
        //@ open post();
      }
    }
  }
}

int main() //@ : custom_main_spec
//@ requires obs({}, {}) &*& module(bounded_fifo, true);
//@ ensures obs(_, {});
//@ terminates;
{
  //@ open_module();
  //@ close call_below_perms(0);
  /*@
  for (int i = 0; i < 100; i++)
    invariant obs({}, {}) &*& 0 <= i &*& i <= 100 &*& call_below_perms(i);
    decreases 100 - i;
  {
    produce_call_below_perm_();
    pathize_call_below_perm_();
    close call_below_perms(i + 1);
  }
  @*/
  //@ close call_below_perms(0);
  /*@
  for (int i = 0; i < 89; i++)
    invariant obs({}, {}) &*& 0 <= i &*& i <= 89 &*& call_below_perms(i);
    decreases 89 - i;
  {
    produce_call_below_perm_();
    pathize_call_below_perm_();
    close call_below_perms(i + 1);
  }
  @*/
  //@ void *sp0 = create_signal(1);
  //@ produce_call_below_perm_();
  //@ pathize_call_below_perm_();
  //@ create_wait_perm(sp0, 1, consumer);
  //@ g.produceSignal = sp0;
  //@ void *sc0 = create_signal(2);
  //@ produce_call_below_perm_();
  //@ pathize_call_below_perm_();
  //@ create_wait_perm(sc0, 2, producer);
  //@ g.consumeSignal = sc0;
  //@ close mutex_inv_aux(100, 100);
  //@ close mutex_inv();
  //@ close exists(0);
  //@ close exists<predicate()>(mutex_inv);
  m = create_mutex();
  //@ leak m |-> _;
  {
    /*@
    predicate producer_pre() =
      [1/2]producerNext |-> 100 &*& [1/2]g.produceSignal |-> sp0 &*& [_]m |-> ?mutex &*& [1/2]mutex(mutex, 0, mutex_inv);
    @*/
    /*@
    produce_function_pointer_chunk thread_run(producer)({}, {pair(sp0, 1)}, producer_pre)() {
      open producer_pre();
      call();
    }
    @*/
    //@ close producer_pre();
    fork(producer);
  }
  consumer();
  return 0;
}
