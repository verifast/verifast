// Example of non-reusable input/output-style verification.
// This program prints "h" and "i" to a buffer of size one, concurrently.
// The result can be "h" or "i", but nothing else.


#include <threading.h>
#include <stdlib.h> // abort() on malloc-fail.
//@ #include "../writer_cat_reader/gcf.gh"
//@ #include "place_iot_no_read.gh"

struct buffer{
  struct mutex *mutex;
  int c;
};

/*@
fixpoint t last<t>(list<t> l){
  switch(l){
    case nil: return default_value<t>;
    case cons(h, tail): return tail == nil ? h : last(tail);
  }
}

predicate_ctor buffer_invar(int id, struct buffer *b)() =
  b->c |-> ?c
  &*& [1/2]gcf_instance(id, iot_split_left(iot_init), ?l)
  &*& [1/2]gcf_instance(id, iot_split_right(iot_init), ?r)
  &*& exists<pair<int, list<int> > >(pair('l', ?l_todo))
  &*& append(l, l_todo) == {'h'}
  &*& exists<pair<int, list<int> > >(pair('r', ?r_todo))
  &*& append(r, r_todo) == {'i'}
  &*& l != nil && r != nil ?
      c == last(l) || c == last(r)
    : r != nil ?
      c == last(r)
    : l != nil ?
      c == last(l)
    : emp;

predicate buffer(int id, struct buffer *b;) =
  b->mutex |-> ?mutex
  &*& mutex(mutex, buffer_invar(id, b));

predicate token_inner(place t1) =
  [1/2]gcf_instance(place_id(t1), place_iot(t1), place_progress(t1))
   &*& iot_is_split_left(place_iot(t1)) || iot_is_split_right(place_iot(t1)) ?
       [1/2]token_inner(place_parent1(t1))
     : iot_is_join(place_iot(t1)) ?
       token_inner(place_parent1(t1))
       &*& token_inner(place_parent2(t1))
     : emp
;

predicate token(struct buffer *b, place t) =
  [iot_fract(place_iot(t))]buffer(place_id(t), b)
  &*& token_inner(t);

predicate putchar_io(place t1, int c, place t2) =
  place_id(t1) == place_id(t2)
  &*& place_iot(t2) == place_iot(t1)
  &*& place_parent1(t2) == place_parent1(t1)
  &*& place_parent2(t2) == place_parent2(t1)
  &*& place_progress(t2) == {c}
  &*& place_progress(t1) == {}
  &*& place_iot(t1) == iot_split_left(iot_init) && c == 'h'
    || place_iot(t1) == iot_split_right(iot_init) && c == 'i';
@*/

void putchar(struct buffer *b, int c)
/*@ requires
      token(b, ?t1)
      &*& putchar_io(t1, c, ?t2);
@*/
/*@ ensures token(b, t2);
@*/
{
  //@ open token(b, t1);
  //@ open [iot_fract(place_iot(t1))]buffer(place_id(t1), b);
  mutex_acquire(b->mutex);
  //@ open buffer_invar(place_id(t1), b)();
  b->c = c;
  
  //@ open putchar_io(t1, c, t2);
  /*@
  if (place_iot(t1) == iot_split_left(iot_init)){
    open exists<pair<int, list<int> > >(pair('l', ?l_todo));
    close exists<pair<int, list<int> > >(pair('l', {}));
  }else{
    open exists<pair<int, list<int> > >(pair('r', ?r_todo));
    close exists<pair<int, list<int> > >(pair('r', {}));
  }
  @*/
  
  //@ open token_inner(t1);
  //@ gcf_update(place_id(t1), place_iot(t1), {c});
  //@ assert place_id(t1) == place_id(t2);
  //@ close token_inner(t2);
  //@ close buffer_invar(place_id(t2), b)();
  mutex_release(b->mutex);
  //@ close [iot_fract(place_iot(t2))]buffer(place_id(t2), b);
  //@ close token(b, t2);
}

/*@
predicate_family_instance thread_run_pre(print_h)(struct buffer *b, any p) =
  p == pair(?t1, ?t2)
  &*& token(b, t1) &*& putchar_io(t1, 'h', t2);
predicate_family_instance thread_run_post(print_h)(struct buffer *b, any p) =
  p == pair(?t1, ?t2)
  &*& token(b, t2);
@*/

void print_h(struct buffer *b) //@ : thread_run_joinable
//@ requires thread_run_pre(print_h)(b, ?p);
//@ ensures thread_run_post(print_h)(b, p);
{
  //@ open thread_run_pre(print_h)(b, p);
  putchar(b, 'h');
  //@ close thread_run_post(print_h)(b, p);
}

void print_i(struct buffer *b)
//@ requires token(b, ?t1) &*& putchar_io(t1, 'i', ?t2);
//@ ensures token(b, t2);
{
  putchar(b, 'i');
}

/*@
predicate split_io(place t1, place t2, place t3) =
  t2 == place(iot_split_left(place_iot(t1)), {}, t1, place_none, place_id(t1))
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t2), place_iot(t2), {})
  &*& t3 == place(iot_split_right(place_iot(t1)), {}, t1, place_none, place_id(t1))
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t3), place_iot(t3), {});

lemma void split()
  requires token(?b, ?t1) &*& split_io(t1, ?t2, ?t3);
  ensures token(b, t2) &*& token(b, t3);
{
  open token(b, t1);
  open split_io(_, _, _);
  close token_inner(t2);
  close token_inner(t3);
  close token(b, t2);
  close token(b, t3);
}

predicate join(place t1, place t2, place t3) =
  t3 == place(iot_join(place_iot(t1), place_iot(t2)), {}, t1, t2, place_id(t1))
  &*& place_id(t1) == place_id(t2) && place_id(t3) == place_id(t2)
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t3), place_iot(t3), {});

lemma void join()
  requires join(?t1, ?t2, ?t3) &*& token(?b, t1) &*& token(b, t2);
  ensures token(b, t3);
{
  open join(_, _, _);
  open token(b, t1);
  open token(b, t2);
  close token_inner(t3);
  close token(b, t3);
}
@*/


void print_hi(struct buffer *b)
/*@ requires token(b, ?t1) &*& split_io(t1, ?th1, ?ti1)
          &*& putchar_io(th1, 'h', ?th2)
          &*& putchar_io(ti1, 'i', ?ti2)
          &*& join(th2, ti2, ?t2); @*/
//@ ensures token(b, t2);
{
  //@ split();
  //@ close thread_run_pre(print_h)(b, pair(th1, th2));
  struct thread *thread = thread_start_joinable(print_h, b);
  print_i(b);
  thread_join(thread);
  //@ open thread_run_post(print_h)(b, pair(th1, th2));
  //@ join();
}


int main()
//@ requires true;
//@ ensures result == 'i' || result == 'h';
{
  struct buffer *b = malloc(sizeof(struct buffer));
  if (b == 0){
    abort();
  }
  //@ int id = create_gcf();
  //@ iot iot1 = iot_init;
  //@ iot ioth = iot_split_left(iot1);
  //@ iot ioti = iot_split_right(iot1);
  //@ iot iot2 = iot_join(ioth, ioti);
  //@ create_gcf_instance(id, iot1, {});
  //@ create_gcf_instance(id, ioth, {});
  //@ create_gcf_instance(id, ioti, {});
  //@ create_gcf_instance(id, iot2, {});
  
  //@ close exists<pair<int, list<int> > >(pair('l', {'h'}));
  //@ close exists<pair<int, list<int> > >(pair('r', {'i'}));
  //@ close buffer_invar(id, b)();
  //@ close create_mutex_ghost_arg(buffer_invar(id, b));
  b->mutex = create_mutex();
  
  //@ close buffer(id, b);
  //@ place t1 = place(iot1, {}, place_none, place_none, id);
  //@ place th1 = place(ioth, {}, t1, place_none, id);
  //@ place th2 = place(ioth, {'h'}, t1, place_none, id);
  //@ place ti1 = place(ioti, {}, t1, place_none, id);
  //@ place ti2 = place(ioti, {'i'}, t1, place_none, id);
  //@ place t2 = place(iot2, {}, th2, ti2, id);
  
  //@ close token_inner(t1);
  //@ close token(b, t1);
  //@ close split_io(t1, th1, ti1);
  //@ close putchar_io(th1, 'h', th2);
  //@ close putchar_io(ti1, 'i', ti2);
  //@ close join(th2, ti2, t2);
  print_hi(b);
  //@ open token(b, t2);
  //@ open buffer(id, b);
  mutex_dispose(b->mutex);
  //@ open buffer_invar(id, b)();
  int x = b->c;
  free(b);
  return x;
  
  // Open to obtain info about progresses.
  // We need this to prove the postcondition.
  //@ open token_inner(_);
  //@ open token_inner(_);
  //@ open token_inner(_);
  //@ open token_inner(_);
  //@ open token_inner(_);
  
  // Leak ghost data
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf(_, _);
  //@ leak exists(_);
  //@ leak exists(_);
}

