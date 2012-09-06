/*@
inductive trace = zero | inc(int, trace) | dec(int, trace) | cas_(int, int, int, trace);

fixpoint bool is_good_prefix(trace pref, trace trace, int ctid) {
  switch(trace) {
    case zero: return pref == zero;
    case inc(tid, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
    case dec(tid, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
    case cas_(tid, old, new, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
  }
}

fixpoint int execute_trace(trace trace) {
  switch(trace) {
    case zero: return 0;
    case inc(tid, trace0): return execute_trace(trace0) + 1;
    case dec(tid, trace0): return execute_trace(trace0) - 1;
    case cas_(tid, old, new, trace0): return execute_trace(trace0) == old ? new : execute_trace(trace0);
  }
}

predicate cell(int* c, fixpoint(trace, bool) allowed);

predicate last_seen(int* c, int tid, trace trace);

lemma int create_atomic_int(int* c, fixpoint(trace, bool) allowed);
  requires integer(c, 0);
  ensures cell(c, allowed);

lemma void last_seen_allowed(int* c, int ctid);
  requires [?f]cell(c, ?allowed) &*& last_seen(c, ctid, ?trace);
  ensures [f]cell(c, allowed) &*& last_seen(c, ctid, trace) &*& allowed(trace) == true;
@*/

/*@
typedef lemma void dec_allowed(trace pretrace, fixpoint(trace, bool) allowed, int ctid)(trace trace);
  requires is_good_prefix(pretrace, trace, ctid) == true &*& allowed(trace) == true;
  ensures allowed(dec(ctid, trace)) == true;
@*/

void atomic_dec(int* c);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace) &*& is_dec_allowed(?lem, oldtrace, allowed, currentThread);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, dec(currentThread, ?currtrace)) &*& is_good_prefix(oldtrace, currtrace, currentThread) == true;
  
int atomic_load(int* c);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, ?currtrace) &*& is_good_prefix(oldtrace, currtrace, currentThread) == true &*& execute_trace(currtrace) == result;
  
/*@
typedef lemma void cas_allowed(trace pretrace, fixpoint(trace, bool) allowed, int old, int new)(trace trace);
  requires is_good_prefix(pretrace, trace, currentThread) == true &*& allowed(trace) == true;
  ensures allowed(cas_(currentThread, old, new, trace)) == true;
@*/
  
int atomic_cas(int* c, int old, int new);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace) &*& is_cas_allowed(?lem, oldtrace, allowed, old, new);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, cas_(currentThread, old, new, ?currtrace)) &*& is_good_prefix(currtrace, currtrace, currentThread) == true &*& result == execute_trace(currtrace);

/*@
fixpoint bool incr_only(trace trace) {
  switch(trace) {
    case zero: return true;
    case inc(tid, trace0): return incr_only(trace0);
    case dec(tid, trace0): return false;
    case cas_(tid, old, new, trace0): return old <= new && incr_only(trace0);
  }
}

lemma void prefix_smaller(trace t1, trace t2, int ctid)
  requires incr_only(t1) == true &*& incr_only(t2) == true &*& is_good_prefix(t1, t2, ctid) == true;
  ensures execute_trace(t1) <= execute_trace(t2);
{
  switch(t2) {
    case zero:
    case inc(tid, t0): if(t1 != t2) prefix_smaller(t1, t0, ctid);
    case dec(tid, t0): 
    case cas_(tid, old, new, t0): if(t1 != t2) prefix_smaller(t1, t0, ctid);
  }
}
@*/

void only_allow_incrementing(int* c)
  //@ requires [?f]cell(c, incr_only) &*& last_seen(c, currentThread, ?trace0);
  //@ ensures [f]cell(c, incr_only) &*& last_seen(c, currentThread, _);
{
  int x1 = atomic_load(c);
  //@ assert last_seen(c, currentThread, ?trace1);
  //@ last_seen_allowed(c, currentThread);
  int x2 = atomic_load(c);
  //@ assert last_seen(c, currentThread, ?trace2);
  //@ last_seen_allowed(c, currentThread);
  //@ prefix_smaller(trace1, trace2, currentThread);
  assert x1 <= x2;
}

/*@
fixpoint option<int> lock_owner(trace trace) {
  switch(trace) {
    case zero: return none;
    case inc(tid, trace0): return none;
    case dec(tid, trace0): return none;
    case cas_(tid, old, new, trace0): return execute_trace(trace0) == old ? some(tid) : lock_owner(trace0);
  }
}

fixpoint bool is_lock(trace trace) {
  switch(trace) {
    case zero: return true;
    case inc(tid, trace0): return false;
    case dec(tid, trace0): return switch(lock_owner(trace0)) { case none: return false; case some(owningtid): return owningtid == tid; } && is_lock(trace0);
    case cas_(tid, old, new, trace0): return old == 0 && new == 1 && is_lock(trace0);
  }
}
@*/

void acquire(int* c)
  //@ requires [?f]cell(c, is_lock) &*& last_seen(c, currentThread, _);
  //@ ensures [f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace1) &*& lock_owner(trace1) == some(currentThread);
{
  while(true)
    //@ invariant [f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace0);
  {
    /*@
    {
      lemma void acquire_ok(trace trace)
        requires is_good_prefix(trace0, trace, currentThread) == true &*& is_lock(trace) == true;
        ensures is_lock(cas_(currentThread, 0, 1, trace)) == true;
      {
        
      }
      produce_lemma_function_pointer_chunk(acquire_ok) : cas_allowed(trace0, is_lock, 0, 1)(x) { call(); };
    }
    @*/
  //@ last_seen_allowed(c, currentThread);
    int read = atomic_cas(c, 0, 1);
    if(read == 0) {
      break;
    }
  }
}

/*@
lemma void execute_steps_locked(trace t)
  requires lock_owner(t) == some(?owner) &*& is_lock(t) == true;
  ensures execute_trace(t) == 1;
{
  switch(t) {
    case zero:
    case inc(tid, trace0):
    case dec(tid, trace0):
    case cas_(tid, old, new, trace0):
      if(execute_trace(trace0) == 0) {
      } else {
        execute_steps_locked(trace0);
      }
  }
}

lemma void locked_preserved_by_interference(trace t1, trace t2, int ctid)
  requires is_good_prefix(t1, t2, ctid) == true &*& lock_owner(t1) == some(ctid) &*& is_lock(t2) == true;
  ensures lock_owner(t2) == some(ctid);
{
  switch(t2) {
    case zero:
    case inc(tid, trace0):
      if(t1 == t2) {
      } else {
        test(t1, trace0, ctid);
      }
    case dec(tid, trace0):
      if(t1 == t2) {
      } else {
        locked_preserved_by_interference(t1, trace0, ctid);
      }
    case cas_(tid, old, new, trace0):
      if(t1 == t2) {
      } else {
        if(tid == ctid) {
        } else {
           locked_preserved_by_interference(t1, trace0, ctid);
           execute_steps_locked(trace0);
        }
      }
  }
}
@*/

void release(int* c)
  //@ requires [?f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace0) &*& lock_owner(trace0) == some(currentThread);
  //@ ensures [f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace1) &*& lock_owner(trace1) == none;
{
  //@ int ctid = currentThread;
  /*@
  {
    lemma void release_ok(trace trace)
      requires is_good_prefix(trace0, trace, ctid) == true &*& is_lock(trace) == true;
      ensures is_lock(dec(ctid, trace)) == true;
    {
      locked_preserved_by_interference(trace0, trace, ctid);
    }
    produce_lemma_function_pointer_chunk(release_ok) : dec_allowed(trace0, is_lock, currentThread)(x) { call(); };
  }
  @*/
  atomic_dec(c);
}




