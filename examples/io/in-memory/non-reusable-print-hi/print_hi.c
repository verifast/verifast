// Example of non-reusable input/output-style verification.
// This program prints "h" and "i" to a buffer of size one, concurrently.
// The result can be "h" or "i", but nothing else.


#include <threading.h>
#include <stdlib.h> // abort() on malloc-fail.
//@ #include "../writer-cat-reader/gcf.gh"


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


inductive iot =
  iot_init
  | iot_split_left(iot)
  | iot_split_right(iot)
  | iot_join(iot, iot);

fixpoint bool iot_is_split_left(iot iot){
  switch(iot){
    case iot_init: return false;
    case iot_join(l, r): return false;
    case iot_split_left(parent): return true;
    case iot_split_right(parent): return false;
  }
}
fixpoint bool iot_is_split_right(iot iot){
  switch(iot){
    case iot_init: return false;
    case iot_join(l, r): return false;
    case iot_split_left(parent): return false;
    case iot_split_right(parent): return true;
  }
}
fixpoint bool iot_is_join(iot iot){
  switch(iot){
    case iot_init: return false;
    case iot_join(l, r): return true;
    case iot_split_left(parent): return false;
    case iot_split_right(parent): return false;
  }
}

// id is kept in place such that split/join predicates can contain
// the [1/2]gcf(id) without having an id argument.
inductive place =
  | place_none
  | place(iot iot, list<int> progress, place parent1, place parent2,
          int id);

fixpoint iot place_iot(place t1){
  switch(t1){
    case place_none: return default_value<iot>;
    case place(iot, progress, parent1, parent2, id): return iot;
  }
}
fixpoint place place_parent1(place t1){
  switch(t1){
    case place_none: return default_value<place>;
    case place(iot, progress, parent1, parent2, id): return parent1;
  }
}
fixpoint place place_parent2(place t1){
  switch(t1){
    case place_none: return default_value<place>;
    case place(iot, progress, parent1, parent2, id): return parent2;
  }
}
fixpoint list<int> place_progress(place t1){
  switch(t1){
    case place_none: return default_value<list<int> >;
    case place(iot, progress, parent1, parent2, id): return progress;
  }
}
fixpoint int place_id(place t1){
  switch(t1){
    case place_none: return default_value<int>;
    case place(iot, progress, parent1, parent2, id): return id;
  }
}

predicate token(place t1) =
  [1/2]gcf_instance(place_id(t1), place_iot(t1), place_progress(t1))
   &*& iot_is_split_left(place_iot(t1)) || iot_is_split_right(place_iot(t1)) ?
       [1/2]token(place_parent1(t1))
     : iot_is_join(place_iot(t1)) ?
       token(place_parent1(t1))
       &*& token(place_parent2(t1))
     : emp
;

predicate putchar_io(int id, place t1, int c, place t2) =
  place_id(t1) == id
  &*& place_id(t2) == id
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
      [?f]buffer(?id, b)
      &*& token(?t1)
      &*& putchar_io(id, t1, c, ?t2);
@*/
/*@ ensures token(t2)
     &*& [f]buffer(id, b);
@*/
{
  //@ open buffer(id, b);
  mutex_acquire(b->mutex);
  //@ open buffer_invar(id, b)();
  b->c = c;
  //@ open putchar_io(id, t1, c, t2);
  //@ open token(t1);
  
  /*@
  if (place_iot(t1) == iot_split_left(iot_init)){
    // note: this merge_fractions needs the branching provided by the if.
    // we put them inside the if to make this clear, although for VeriFast
    // it'll also work if they are put after the if because the branching
    // that VeriFast performs continues after the if.
    merge_fractions(gcf_instance(id, iot_split_left(iot_init), _));
    merge_fractions(gcf_instance(id, iot_split_right(iot_init), _));
    open exists<pair<int, list<int> > >(pair('l', ?l_todo));
    close exists<pair<int, list<int> > >(pair('l', {}));
  }else{
    merge_fractions(gcf_instance(id, iot_split_left(iot_init), _));
    merge_fractions(gcf_instance(id, iot_split_right(iot_init), _));
    open exists<pair<int, list<int> > >(pair('r', ?r_todo));
    close exists<pair<int, list<int> > >(pair('r', {}));
  }
  @*/
    
  //@ gcf_update(id, place_iot(t1), {c});
  //@ assert place_id(t1) == place_id(t2);
  //@ close token(t2);
  //@ close buffer_invar(id, b)();
  mutex_release(b->mutex);
  //@ close [f]buffer(id, b);
}

/*@

predicate_family_instance thread_run_pre(print_h)(struct buffer *b, any p) =
  p == pair(?f, pair(?id, pair(?t1, ?t2)))
  &*& [f]buffer(id, b) &*& token(t1) &*& putchar_io(id, t1, 'h', t2);
predicate_family_instance thread_run_post(print_h)(struct buffer *b, any p) =
  p == pair(?f, pair(?id, pair(?t1, ?t2)))
  &*& [f]buffer(id, b) &*& token(t2);
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
//@ requires [?f]buffer(?id, b) &*& token(?t1) &*& putchar_io(id, t1, 'i', ?t2);
//@ ensures [f]buffer(id, b) &*& token(t2);
{
  putchar(b, 'i');
}

/*@
predicate split(place t1, place t2, place t3) =
  t2 == place(iot_split_left(place_iot(t1)), {}, t1, place_none, place_id(t1))
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t2), place_iot(t2), {})
  &*& t3 == place(iot_split_right(place_iot(t1)), {}, t1, place_none, place_id(t1))
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t3), place_iot(t3), {});

lemma void split()
  requires token(?t1) &*& split(t1, ?t2, ?t3);
  ensures token(t2) &*& token(t3);
{
  open split(_, _, _);
  close token(t2);
  close token(t3);
}

predicate join(place t1, place t2, place t3) =
  t3 == place(iot_join(place_iot(t1), place_iot(t2)), {}, t1, t2, place_id(t1))
  // We don't actually need t1.id == t2.id because the io(id, t1, t2)-predicates
  // will connect id with the ids stored in the places, so if the ids don't match
  // you won't be able to link the progresses of the places with the progresses of the invar.
  &*& [1/2]gcf_instance<iot, list<int> >(place_id(t3), place_iot(t3), {});

lemma void join()
  requires join(?t1, ?t2, ?t3) &*& token(t1) &*& token(t2);
  ensures token(t3);
{
  open join(_, _, _);
  close token(t3);
}

@*/


void print_hi(struct buffer *b)
/*@ requires [?f]buffer(?id, b) &*& token(?t1) &*& split(t1, ?th1, ?ti1)
          &*& putchar_io(id, th1, 'h', ?th2)
          &*& putchar_io(id, ti1, 'i', ?ti2)
          &*& join(th2, ti2, ?t2); @*/
//@ ensures [f]buffer(id, b) &*& token(t2);
{
  //@ split();
  //@ close thread_run_pre(print_h)(b, pair(f/2, pair(id, pair(th1, th2))));
  struct thread *thread = thread_start_joinable(print_h, b);
  print_i(b);
  thread_join(thread);
  //@ open thread_run_post(print_h)(b, pair(f/2, pair(id, pair(th1, th2))));
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
  
  //@ close token(t1);
  //@ close split(t1, th1, ti1);
  //@ close putchar_io(id, th1, 'h', th2);
  //@ close putchar_io(id, ti1, 'i', ti2);
  //@ close join(th2, ti2, t2);
  
  print_hi(b);
  //@ open buffer(id, b);
  mutex_dispose(b->mutex);
  //@ open buffer_invar(id, b)();
  int x = b->c;
  free(b);
  return x;
  
  // Open tokens to obtain info about progresses.
  // We need this to prove the postcondition.
  //@ open token(_);
  //@ open token(_);
  //@ open token(_);
  //@ open token(_);
  //@ open token(_);
  
  // Leak ghost data
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf_instance(_, _, _);
  //@ leak gcf(_, _);
  //@ leak exists(_);
  //@ leak exists(_);
}

