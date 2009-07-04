#include "stdlib.h"
#include "threading.h"

struct counter {
  int x;
  //@ int contrib1;
  //@ int contrib2;
};

/*@

predicate_ctor counter(struct counter* c)()
  requires c->x |-> ?v &*& [1/2]c->contrib1 |-> ?c1 &*& [1/2]c->contrib2 |-> ?c2 &*& v == c1 + c2;

@*/

struct session {
  bool isFirst;
  struct lock* lock;
  struct counter* counter;
};

/*@

predicate session(struct session *session; bool isFirst, struct lock *lock, struct counter *counter) =
  session->isFirst |-> isFirst &*& session->lock |-> lock &*& session->counter |-> counter &*& malloc_block_session(session);

@*/


struct session* create_session(struct lock* lock, struct counter* counter, bool isFirst)
  //@ requires true;
  //@ ensures session(result, isFirst, lock, counter);
{
  struct session* s = malloc(sizeof(struct session));
  if (s == 0) { abort(); }
  s->isFirst = isFirst;
  s->lock = lock;
  s->counter = counter;
  //@ close session(s, isFirst, lock, counter);
  return s;
}

/*@

predicate_family_instance thread_run_pre(inc)(struct session* s)
  requires [1/2]session(s, ?isFirst, ?lock, ?counter) &*&
           [1/4]lock_permission(lock, counter(counter)) &*& isFirst ? [1/2]counter->contrib1 |-> 0 : [1/2]counter->contrib2 |-> 0;
  
predicate_family_instance thread_run_post(inc)(struct session* s)
  requires [1/2]session(s, ?isFirst, ?lock, ?counter) &*&
           [1/4]lock_permission(lock, counter(counter)) &*& isFirst ? [1/2]counter->contrib1 |-> 1 : [1/2]counter->contrib2 |-> 1;

@*/

void inc(void* data) //@ : thread_run
  //@ requires thread_run_pre(inc)(data);
  //@ ensures thread_run_post(inc)(data);
{
  struct session* session = data;
  //@ open thread_run_pre(inc)(session);
  //@ open [1/2]session(session, ?isFirst, ?lock, ?counter);
  lock_acquire(session->lock);
  struct counter* c = session->counter;
  //@ open counter(c)();
  c->x = c->x + 1;
  if(session->isFirst) {
    //@ merge_fractions counter_contrib1(c, _);
    c->contrib1 = c->contrib1 + 1;
    //@ split_fraction counter_contrib1(c, _);
  } else {
    //@ merge_fractions counter_contrib2(c, _);
    c->contrib2 = c->contrib2 + 1;
    //@ split_fraction counter_contrib2(c, _);
  }
  //@ close counter(c)();
  lock_release(session->lock);
  //@ close [1/2]session(session, isFirst, lock, counter);
  //@ close thread_run_post(inc)(data);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct counter* c = malloc(sizeof(struct counter));
  if(c == 0) { abort(); }
  c->x = 0;
  c->contrib1 = 0;
  c->contrib2 = 0;
  //@ split_fraction counter_contrib1(c, _);
  //@ split_fraction counter_contrib2(c, _);
  //@ close counter(c)();

  //@ close create_lock_ghost_argument(counter(c));
  struct lock* l = create_lock();
  
  //@ split_fraction lock_permission(l, _);
  //@ split_fraction lock_permission(l, _);
  
  struct session* s1 = create_session(l, c, true);
  //@ split_fraction session(s1, _, _, _);
  //@ close thread_run_pre(inc)(s1);
  struct thread* t1 = thread_start(inc, s1);
  
  struct session* s2 = create_session(l, c, false);
  //@ split_fraction session(s2, _, _, _);
  //@ close thread_run_pre(inc)(s2);
  struct thread* t2 = thread_start(inc, s2);
  
  thread_join(t1);
  //@ open thread_run_post(inc)(s1);
  //@ merge_fractions session(s1, _, _, _);
  //@ open session(s1, _, _, _);
  
  thread_join(t2);
  //@ open thread_run_post(inc)(s2);
  //@ merge_fractions session(s2, _, _, _);
  //@ open session(s2, _, _, _);

  //@ merge_fractions lock_permission(l, _);
  //@ merge_fractions lock_permission(l, _);
  lock_dispose(l);
  //@ open counter(c)();
  //@ merge_fractions counter_contrib1(c, _);
  //@ merge_fractions counter_contrib2(c, _);
  
  int tmp = c->x;
  assert(tmp == 2);
  
  free(s1);
  free(s2);
  free(c);
  return 0;
}