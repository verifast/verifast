#include "stdlib.h"
#include "threading.h"

struct counter {
  int x;
  //@ int contrib1;
  //@ int contrib2;
};

/*@
predicate counter(struct counter* c, int v)
  requires c->x |-> v &*& malloc_block_counter(c) &*& [1/2]c->contrib1 |-> ?c1 &*& [1/2]c->contrib2 |-> ?c2 &*& v == c1 + c2;
  
predicate_ctor counter_ctor(struct counter* c)()
  requires counter(c, _); 
  
predicate session(struct session* s)
  requires [1/2]s->isFirst |-> ?b &*& s->lock |-> ?l &*& [1/2]s->counter |-> ?c &*& malloc_block_session(s) &*&
           lock_permission(l, counter_ctor(c)) &*& b == true ? [1/2] c->contrib1 |-> 0 : [1/2] c->contrib2 |-> 0;

predicate session_done(struct session* s)
  requires [1/2]s->isFirst |-> ?b &*& s->lock |-> ?l &*& [1/2]s->counter |-> ?c &*& malloc_block_session(s) &*&
           lock_permission(l, counter_ctor(c)) &*& b == true ? [1/2] c->contrib1 |-> 1 : [1/2] c->contrib2 |-> 1;

predicate_family_instance thread_run_data(inc)(void* data)
  requires session(data);
  
predicate_family_instance thread_run_post(inc)(void* data)
  requires session_done(data);

@*/

struct session {
  bool isFirst;
  struct lock* lock;
  struct counter* counter;
};

struct session* create_session(struct lock* l, struct counter* c, bool b)
  //@ requires lock_permission(l, counter_ctor(c)) &*& b == true ? [1/2] c->contrib1 |-> 0 : [1/2]c->contrib2 |-> 0;
  //@ ensures session(result) &*& [1/2]result->isFirst |->b &*& [1/2]result->counter |->c;
{
  struct session* s = malloc(sizeof(struct session));
  if(s == 0) { abort(); }
  s->isFirst = b;
  s->lock = l;
  s->counter = c;
  //@ split_fraction session_isFirst(s, b);
  //@ split_fraction session_counter(s, c);
  //@ close session(s);  
  return s;
}

void inc(void* data) //@ : thread_run
  //@ requires thread_run_data(inc)(data);
  //@ ensures thread_run_post(inc)(data);
{
  //@ open thread_run_data(inc)(data);
  struct session* session = data;
  //@ open session(data);
  lock_acquire(session->lock);
  //@ open_lock_invariant();
  struct counter* c = session->counter;
  //@ open counter_ctor(c)();
  //@ open counter(c, ?v);
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
  //@ close counter(c, v + 1);
  //@ close counter_ctor(c)();
  //@ close_lock_invariant(counter_ctor(c));
  lock_release(session->lock);  
  //@ close session_done(data);
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
  //@ close counter(c, 0);
  
  //@ close counter_ctor(c)();
  //@ close_lock_invariant(counter_ctor(c));
  
  struct lock* l = create_lock();
  
  //@ split_lock_permission(l);
  //@ split_lock_permission(l);
  
  struct session* s1 = create_session(l, c, true);
  struct session* s2 = create_session(l, c, false);
  
  //@ close thread_run_data(inc)(s1);
  struct thread* t1 = thread_start(inc, s1);
  
  //@ close thread_run_data(inc)(s2);
  struct thread* t2 = thread_start(inc, s2);
  
  thread_join(t1);
  //@ open thread_run_post(inc)(s1);
  //@ open session_done(s1);
  //@ merge_fractions session_isFirst(s1, _);
  //@ merge_fractions session_counter(s1, _);
  
  thread_join(t2);
  //@ open thread_run_post(inc)(s2);
  //@ open session_done(s2);
  //@ merge_fractions session_isFirst(s2, _);
  //@ merge_fractions session_counter(s2, _);

  lock_acquire(l);
  //@ open_lock_invariant();
  //@ open counter_ctor(c)();
  //@ open counter(c, _);
  //@ merge_fractions counter_contrib1(c, _);
  //@ merge_fractions counter_contrib2(c, _);
  
  int tmp = c->x;
  assert tmp == 2; // this assertion succeeds!
  
  abort(); // todo: empty the heap!
  return 0;
}