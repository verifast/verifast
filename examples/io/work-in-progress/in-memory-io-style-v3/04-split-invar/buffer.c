/**
 * "split-invar" approach.
 *
 * TODO THIS IS A DRAFT PROTOTYPE!
 * 
 * Nice properties:
 * + Supports split and join (contrary to the "weak" approach)
 * + function does not know what they are used for (contrary to weak)
 *   and are thus reusable
 * + threads can (but do not have to) have knowledge what the other threads
 *   do, e.g. a reader can know it will never read a negative number because
 *   the writer never writes one (like weak, contrary to framepresupd)
 * + reading works (using prophecies)
 * + underspecification should just work (but untested)
 * + invariant, which links together the ghost-threads, does not have to be complex
 *   (contrary to e.g. IGR)
 *
 * TODO
 * - compositionaly: just works if they all share the same invariant, otherwise TODO
 * - support nonterminating programs (closing copredicates)
 * - make parts expected to be generic, generic
 * - more examples to get a better feeling with this approach and showcase more
 * - cleanup
 *
 * Issues:
 * - as with all in-memory split/join: high annotation overhead
 * - lemma function pointer chunks are awkward to use
 * 
 * This is an example on a circular buffer.
 */


#include <malloc.h>
#include <stdlib.h> // abort()
//@ #include "prophecy.gh"

#include "../../../../vstte2012/problem3/problem3.h" // Ring buffer
#include <threading.h>
#include "io.h"
//@ #include "../../in-memory-io-style-v1.1/io/helpers/ghost_mutex.gh"
//@ #include <listex.gh>

struct buffer {
  struct ring_buffer *ring_buffer;
  struct mutex *mutex;
  struct mutex_cond *cond_can_push;
  struct mutex_cond *cond_can_pop;
};

/*@
predicate_ctor buffer_protected(int family, predicate(int family, list<int> contents) the_invariant, struct buffer *buffer)() =
  buffer->ring_buffer |-> ?ring_buffer
  &*& ring_buffer(ring_buffer, ?size, ?contents)
  &*& the_invariant(family, contents);

predicate buffer(int family, predicate(int family, list<int> contents) the_invariant, struct buffer *buffer;) =
  buffer-> mutex|-> ?mutex
  &*& mutex(mutex, ((buffer_protected)(family, the_invariant, buffer)))
  &*& buffer->cond_can_push |-> ?cond_can_push
  &*& mutex_cond(cond_can_push, mutex)
  &*& buffer->cond_can_pop |-> ?cond_can_pop
  &*& mutex_cond(cond_can_pop, mutex)
  &*& malloc_block_buffer(buffer);
@*/

/*@
predicate create_buffer_ghost_arg(int family, predicate(int family, list<int> contents) the_invariant) = true;
@*/
struct buffer *create_buffer(int size)
/*@ requires
  size > 0 &*& size * sizeof(int) < INT_MAX &*& create_buffer_ghost_arg(?family, ?the_invariant)
  &*& [1/2]progress(id_init(family), nil)
  &*& the_invariant(family, nil)
  &*& token_opaque(place_init(family));
@*/
/*@ ensures
  result == 0 ?
    [1/2]progress(id_init(family), nil)
    &*& the_invariant(family, nil)
    &*& token_opaque(place_init(family))
  :
    buffer(family, the_invariant, result)
    &*& token(place(id_init(family), no_place, no_place, nil, nil));
@*/
{
  //@ open create_buffer_ghost_arg(_, _);
  struct buffer *buffer = malloc(sizeof(struct buffer));
  if (buffer == 0){
    return 0;
  }
  struct ring_buffer *ring_buffer = ring_buffer_create(size);
  if (ring_buffer == 0){
    free(buffer);
    return 0;
  }
  buffer->ring_buffer = ring_buffer;
  //@ close buffer_protected(family, the_invariant, buffer)();
  //@ close create_mutex_ghost_arg(buffer_protected(family, the_invariant, buffer));
  buffer->mutex = create_mutex();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_push = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(buffer->mutex);
  buffer->cond_can_pop = create_mutex_cond();

  return buffer;
  //@ close buffer(family, the_invariant, buffer);
  //@ close token(place(id_init(family), no_place, no_place, nil, nil));
}

/*@
fixpoint bool push_io_fp(int c, list<int> input, list<int> output) {
  return output == append(input, {c});
}

predicate push_io(place t1, int c, int family, predicate(int, list<int>) the_invariant, place t2) =
  t2 == place_io(t1, (push_io_fp)(c), append(place_progress(t1), {c}))
  // There is a proof that the invariant is updatadble
  &*& is_invar_updatable(?f, (push_io_fp)(c), t1, the_invariant, t2)
  &*& family == id_family(place_id(t1))
  ;
@*/


/** add to end of queue */
void push(struct buffer *buffer, int x)
/*@ requires
  [?f]buffer(?family, ?the_invariant, buffer)
  &*& token(?t1)
  &*& push_io(t1, x, family, the_invariant, ?t2);
@*/
/*@ ensures
  [f]buffer(family, the_invariant, buffer)
  &*& token(t2);
@*/
{
  //@ open buffer(_, _, _);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(family, the_invariant, buffer)();
  //@ open token(t1);
  //@ assert [1/2]progress(place_id(t1), _);
  while (ring_buffer_is_full(buffer->ring_buffer))
  /*@ invariant
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_push |-> ?cond_can_push
      &*& [f]mutex_cond(cond_can_push, mutex)
      &*& the_invariant(family, contents)
      &*& mutex_held(mutex, (buffer_protected)(family, the_invariant, buffer), currentThread, f)
      ;
  @*/
  {
    //@ close buffer_protected(family, the_invariant, buffer)();
    mutex_cond_wait(buffer->cond_can_push, buffer->mutex);
    //@ open buffer_protected(family, the_invariant, buffer)();
  }
  
  bool was_empty = ring_buffer_is_empty(buffer->ring_buffer);
  
  ring_buffer_push(buffer->ring_buffer, x);
  
  if (was_empty){
    mutex_cond_signal(buffer->cond_can_pop);
  }
  //@ open push_io(t1, x, family, the_invariant, t2);
  //@ assert is_invar_updatable(?invar_updater, (push_io_fp)(x), t1, the_invariant, t2);
  //@ assert the_invariant(?id_invar, _);
  //@ assert id_invar == id_family(place_id(t1));
  //@ assert ring_buffer(_, _, ?new_contents);
  //@ close exists(new_contents);
  //@ invar_updater();
  //@ close token(t2);
  //@ close buffer_protected(family, the_invariant, buffer)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(family, the_invariant, buffer);
  //@ leak is_invar_updatable(invar_updater, _, _, _, _);
}

/*@
fixpoint bool pop_io_fp(int c, list<int> input, list<int> output) {
  return output == tail(input) && c == head(input);
}

predicate pop_io(place t1, int c, int family, predicate(int, list<int>) the_invariant, place t2) =
  t2 == place_io(t1, (pop_io_fp)(c), tail(place_progress(t1)))
  // There is a proof that the invariant is updatadble
  &*& is_invar_updatable(?f, (pop_io_fp)(c), t1, the_invariant, t2)
  &*& family == id_family(place_id(t1))
  &*& prophecy(c, family, the_invariant, pop_io_fp);
@*/

/*@
typedef lemma void read_proof_pop(int family, predicate(int, list<int>) the_invariant, int c, fixpoint(int, list<int>, list<int>, bool) fp, predicate() p, place t1)();
  requires the_invariant(family, ?contents) &*& contents != nil
    &*& pop_io(t1, c, family, the_invariant, ?t2);
  ensures the_invariant(family, contents) // TODO: allow content change to allow more invariants?
    &*& pop_io(t1, c, family, the_invariant, t2)
    &*& p();
@*/

/** read from beginning of queue (and remove that element) */
int pop(struct buffer *buffer)
/*@ requires
  [?f]buffer(?family, ?the_invariant, buffer)
  &*& token(?t1)
  &*& pop_io(t1, ?c, family, the_invariant, ?t2)
  &*& is_read_proof_pop(?proof, family, the_invariant, c, pop_io_fp, ?p, t1);
@*/
/*@ ensures
  [f]buffer(family, the_invariant, buffer)
  &*& token(t2)
  &*& result == c
  &*& p();
@*/
{
  //@ open buffer(_, _, _);
  //@ assert [f]buffer->mutex |-> ?mutex;
  mutex_acquire(buffer->mutex);
  //@ open buffer_protected(family, the_invariant, buffer)();
  //@ open token(_);
  while (ring_buffer_is_empty(buffer->ring_buffer))
  /*@ invariant
      
      buffer->ring_buffer |-> ?ring_buffer
      &*& [f]buffer->mutex |-> mutex
      &*& ring_buffer(ring_buffer, ?size, ?contents)
      &*& [f]buffer->cond_can_pop |-> ?cond_can_pop
      &*& [f]mutex_cond(cond_can_pop, mutex)
      &*& mutex_held(mutex, (buffer_protected)(family, the_invariant, buffer), currentThread, f)
      &*& the_invariant(family, contents)
      ;
  @*/
  {
    //@ close buffer_protected(family, the_invariant, buffer)();
    mutex_cond_wait(buffer->cond_can_pop, buffer->mutex);
    //@ open buffer_protected(family, the_invariant, buffer)();
  }
  
  bool was_full = ring_buffer_is_full(buffer->ring_buffer);
  
  int x = ring_buffer_pop(buffer->ring_buffer);
  
  if (was_full){
    mutex_cond_signal(buffer->cond_can_push);
  }
  
  //@ proof();
  
  //@ open pop_io(t1, c, family, the_invariant, t2);
  
  //@ assert is_invar_updatable(?invar_updater, (pop_io_fp)(c), t1, the_invariant, t2);
  //@ close exists(tail(contents));
  //@ prophecy_assign<int, list<int> >(c, x);
  //@ close exists(tail(contents));
  //@ invar_updater();
  //@ close token(t2);
  //@ close buffer_protected(family, the_invariant, buffer)();
  mutex_release(buffer->mutex);
  //@ close [f]buffer(family, the_invariant, buffer);
  
  //@ leak is_invar_updatable(_, _, _, _, _);
  //@ leak is_read_proof_pop(_, _, _, _, _, _, _);
  return x;
}

/*@
predicate example_invariant(int family, list<int> contents) =
  invar_opaque(family, contents)
  &*& [1/2]progress(id_init(family), ?progress)
;
@*/

void write_12(struct buffer *buffer)
/*@ requires [?f]buffer(?family, ?the_invariant, buffer)
  &*& push_io(?t1, 1, family, the_invariant, ?t2) &*& push_io(t2, 2, family, the_invariant, ?t3) &*& token(t1);
@*/
/*@ ensures [f]buffer(family, the_invariant, buffer)
  &*& token(t3);
@*/
{
  push(buffer, 1);
  push(buffer, 2);
}



void write_12_and_build_io_contract()
//@ requires true;
//@ ensures true;
{
  //@ int family = create_initial_progress(nil);
  //@ close example_invariant(family, nil);
  //@ close create_buffer_ghost_arg(family, example_invariant);
  struct buffer *buffer = create_buffer(10);
  if (buffer == 0){ abort (); }
  //@ assert token(?t1);
  //@ place t2 = place_io(t1, (push_io_fp)(1), {1});
  /*@ produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(1), t1, example_invariant, t2)() {
    open example_invariant(_, ?state);
    assert exists<list<int> >(?out);
    update_progress(id_init(family), {1});
    io_opaque(family, t1, (push_io_fp)(1), append(state, {1}), {1});
    close example_invariant(family, out);
    call ();
  };
  @*/
  //@ close push_io(t1, 1, family, example_invariant, t2);
  //@ place t3 = place_io(t2, (push_io_fp)(2), {1, 2});
  /*@ produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(2), t2, example_invariant, t3)() {
    open example_invariant(_, ?state);
    assert exists<list<int> >(?out);
    update_progress(id_init(family), {1,2});
    io_opaque(family, t2, (push_io_fp)(2), append(state, {2}), {1,2});
    close example_invariant(family, out);
    call();
  };
  @*/
  //@ close push_io(t2, 2, family, example_invariant, t3);
  write_12(buffer);
  //@ leak buffer(_, _, _);
  //@ leak can_create_progress(_, _);
  //@ leak token(t3);
}


//@ predicate_ctor positive(int c)() = c >= 0;
/**
 * pop but crashes if negative number popped. Verified to never crash. Uses knowledge of the invariant.
 */
int pop_positive(struct buffer *buffer)
/*@
requires [?f]buffer(?family, example_split_invariant, buffer)
  &*& token(?t1) &*& pop_io(t1, ?c, family, example_split_invariant, ?t2);
@*/
/*@
ensures [f]buffer(family, example_split_invariant, buffer) &*& token(t2);
@*/
{
  /*@ 
  produce_lemma_function_pointer_chunk(empty_lemma) : read_proof_pop(family, example_split_invariant, c, pop_io_fp, positive(c), t1)() {
    assert example_split_invariant(family, ?contents);
    open pop_io(t1, c, family, example_split_invariant, ?t2_);
    prophecy_holds(c, head(contents), tail(contents));
    open example_split_invariant(family, contents);
    assert true==forall(contents, (lte)(0));
    switch(contents){ // force VeriFast to branch, kind of "open the forall".
      case nil:
      case cons(ahead, atail):
    }
    close pop_io(t1, c, family, example_split_invariant, t2_);
    close example_split_invariant(family, contents);
    close positive(c)();
    call ();
  };
  @*/

  int x = pop(buffer);
  //@ open positive(c)();
  if (x < 0){
    int *nullptr = 0;
    *nullptr = 123; // crash (we prove that this never happens)
  }
  return x;
}

void split_write_1212_read(struct buffer *buffer)
/*@ requires [?f]buffer(?family, example_split_invariant, buffer)
  &*& token(?t1) &*& split(family, example_split_invariant, buffer, t1, ?ta_1, ?tb_1)
  &*& push_io(ta_1, 1, family, example_split_invariant, ?ta_2) &*& push_io(ta_2, 2, family, example_split_invariant, ?ta_3) // can be put in one predicate
  &*& push_io(tb_1, 1, family, example_split_invariant, ?tb_2) &*& push_io(tb_2, 2, family, example_split_invariant, ?tb_3)
  &*& join(family, example_split_invariant, buffer, ta_3, tb_3, ?t2)
  &*& pop_io(t2, ?c, family, example_split_invariant, ?t3) // note: only here knowledge that it is this invariant is necessary
  ;
@*/
/*@ ensures
  [f]buffer(family, example_split_invariant, buffer)
  &*& token(t3);
@*/
{
  //@ split(t1);
  write_12(buffer);
  write_12(buffer); // can be in a different thread.
  //@ join(ta_3);
  pop_positive(buffer);
}

/*@
fixpoint bool lte(int v1, int v2){
  return v1 <= v2;
}

predicate example_split_invariant(int family, list<int> contents) =
  invar_opaque(family, contents)
  &*& [1/2]progress(id_init(family), ?progress_before_split)
  &*& [1/2]progress(id_split_left(id_init(family)), ?progress_left)
  &*& [1/2]progress(id_split_right(id_init(family)), ?progress_right)
  &*& [1/2]progress(id_join(id_split_left(id_init(family)), id_split_right(id_init(family))), ?progress_join)
  
  &*& progress_before_split == {}
  // ... (optional)
  
  // here, reader simply knows all values are greater than or equal to 0.
  &*& true==forall(contents, (lte)(0))
;
@*/


void split_write_1212_and_build_io_contract()
//@ requires true;
//@ ensures true;
{
  //@ int family = create_initial_progress({});
  //@ create_progress(id_split_left(id_init(family)));
  //@ create_progress(id_split_right(id_init(family)));
  //@ create_progress(id_join( id_split_left(id_init(family)),  id_split_right(id_init(family))  ));
  //@ close example_split_invariant(family, {});
  //@ close create_buffer_ghost_arg(family, example_split_invariant);
  struct buffer *buffer = create_buffer(10);
  if (buffer == 0){ abort (); }
  //@ assert token(?t1);
  //@ close split(family, example_split_invariant, buffer, t1, ?ta_1, ?tb_1);
  //@ place ta_2 = place_io(ta_1, (push_io_fp)(1), {1});
  /*@ 
  produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(1), ta_1, example_split_invariant, ta_2)() {
    open example_split_invariant(_, ?contents);
    assert exists<list<int> >(?out);
    update_progress(id_split_left(id_init(family)), {1});
    forall_append(contents, {1}, (lte)(0));
    io_opaque(family, ta_1, (push_io_fp)(1), append(contents, {1}), {1});
    close example_split_invariant(family, out);
    call ();
  };
  @*/
  //@ close push_io(ta_1, 1, family, example_split_invariant, ta_2);
  //@ place ta_3 = place_io(ta_2, (push_io_fp)(2), {1,2});
  /*@ 
  produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(2), ta_2, example_split_invariant, ta_3)() {
    open example_split_invariant(_, ?contents);
    assert exists<list<int> >(?out);
    update_progress(id_split_left(id_init(family)), {1,2});
    forall_append(contents, {2}, (lte)(0));
    io_opaque(family, ta_2, (push_io_fp)(2), append(contents, {2}), {1,2});
    close example_split_invariant(family, out);
    call ();
  };
  @*/
  //@ close push_io(ta_2, 2, family, example_split_invariant, ta_3);
  //@ place tb_2 = place_io(tb_1, (push_io_fp)(1), {1});
  /*@ 
  produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(1), tb_1, example_split_invariant, tb_2)() {
    open example_split_invariant(_, ?contents);
    assert exists<list<int> >(?out);
    update_progress(id_split_right(id_init(family)), {1});
    forall_append(contents, {1}, (lte)(0));
    io_opaque(family, tb_1, (push_io_fp)(1), append(contents, {1}), {1});
    close example_split_invariant(family, out);
    call ();
  };
  @*/
  //@ close push_io(tb_1, 1, family, example_split_invariant, tb_2);
  //@ place tb_3 = place_io(tb_2, (push_io_fp)(2), {1,2});
  /*@ 
  produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((push_io_fp)(2), tb_2, example_split_invariant, tb_3)() {
    open example_split_invariant(_, ?contents);
    assert exists<list<int> >(?out);
    update_progress(id_split_right(id_init(family)), {1,2});
    forall_append(contents, {2}, (lte)(0));
    io_opaque(family, tb_2, (push_io_fp)(2), append(contents, {2}), {1,2});
    close example_split_invariant(family, out);
    call ();
  };
  @*/
  //@ close push_io(tb_2, 2, family, example_split_invariant, tb_3);
  //@ close join(family, example_split_invariant, buffer, ta_3, tb_3, ?t2);
  
  //@ int c = prophecy_create(family, example_split_invariant, pop_io_fp);
  //@ place t3 = place_io(t2, (pop_io_fp)(c), {});
  /*@
  produce_lemma_function_pointer_chunk(empty_lemma) : invar_updatable((pop_io_fp)(c), t2, example_split_invariant, t3)() {
    open example_split_invariant(_, ?contents);
    assert exists<list<int> >(?out);
    assert out == tail(contents);
    switch(contents){ // force VeriFast to branch, kind of "open the forall".
      case nil:
      case cons(ahead, atail):
    }
    io_opaque(family, t2, (pop_io_fp)(c), tail(contents), {});
    close example_split_invariant(family, out);
    call ();
  };
  @*/
  //@ close pop_io(t2, c, family, example_split_invariant, t3);
  
  split_write_1212_read(buffer);
  
  //@ leak can_create_progress(_, _);
  //@ leak token(_);
  //@ leak buffer(_, _, _);
}
