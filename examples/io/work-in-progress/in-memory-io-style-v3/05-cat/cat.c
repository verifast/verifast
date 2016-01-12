/**
 * Example of in-memory i/o-style verification.
 *
 * This example has a producer (which writes to a buffer),
 * a "cat" thread (that reads from that buffer and writes to
 * another buffer), and a consumer (that reads from the latter buffer).
 *
 * There is one global lock, and there is no compositionality
 * (the code for the buffer is not completely reused): there is
 * a separate write function for the two buffers.
 */
 
#include "io.h"
#include "ids.h"
#include "prophecy.gh"

#include <malloc.h>
#include <stdlib.h> // abort()
#include <threading.h>
//@ #include <ghost_cells.gh>
//@ #include <listex.gh>

#include "../../../../vstte2012/problem3/problem3.h" // Ring buffer

struct system {
  struct mutex *mutex;
  
  struct ring_buffer *ring_buffer1;
  struct mutex_cond *cond_can_push1;
  struct mutex_cond *cond_can_pop1;
  
  struct ring_buffer *ring_buffer2;
  struct mutex_cond *cond_can_push2;
  struct mutex_cond *cond_can_pop2;
};

/*@
predicate write1_io(place t1, int c, place t2) =
  t2 == place_io(t1, c)
  &*& is_can_write1(?f, c, t1, t2);

predicate_ctor read2_io_proph_invar(place t1, int ghost_cell_buf1, int ghost_cell_buf2)(int c) =
  [1/2]ghost_cell<list<int> >(ghost_cell_buf1, ?buffer1_contents) // such that after using this invar, one can prove buffer1_contents stays the same.
  &*& [1/2]ghost_cell<list<int> >(ghost_cell_buf2, ?buffer2_contents)
  &*& [1/2]token(t1, ?family, ?system) // [1/2] to allow to prove that family and system remains the same.
  &*& system_invariant_inner(family, system, buffer1_contents, buffer2_contents)
  &*& buffer2_contents != nil
  &*& c == head(buffer2_contents);

predicate read2_io(place t1, int c, place t2) =
  t2 == place_io(t1, c)
  &*& is_can_read2(?f, c, t1, t2)
  &*& exists<pair<list<char>, int > >(pair("ghost_cell_buf1", ?ghost_cell_buf1))
  &*& ghost_cell<list<int> >(ghost_cell_buf1, _)
  &*& ghost_cell<list<int> >(?ghost_cell_buf2, _)
  &*& prophecy(c, (read2_io_proph_invar)(t1, ghost_cell_buf1, ghost_cell_buf2));

predicate writestr_io(place t1, list<int> writethis, place t2) = 
  writethis == nil ?
    t1 == t2 // note: this will break choice, but we don't need it here.
  :
    write1_io(t1, head(writethis), ?tx)
    &*& writestr_io(tx, tail(writethis), t2);

predicate readstr_io(place t1, int count, list<int> readthis, int sum, place t2) =
  sum == fold_left(0, plus, readthis)
  &*& count <= 0 ?
    t2 == t1
    &*& sum == 0
    &*& readthis == nil
  : read2_io(t1, head(readthis), ?tx)
    &*& readstr_io(tx, count - 1, tail(readthis), ?tailsum, t2)
    &*& readthis != nil
    &*& sum == head(readthis) + tailsum;

predicate cat_io(place t_cat_split, list<int> readwrite, place t_cat_join) =
  split(t_cat_split, ?t_cat_read1, ?t_cat_write1)
    &*& readstr_io(t_cat_read1, length(readwrite), readwrite, ?sum, ?t_cat_read2)
    &*& writestr_io(t_cat_write1, readwrite, ?t_cat_write2)
  &*& join(t_cat_read2, t_cat_write2, t_cat_join);

predicate system_io(place t_splitA, list<int> text, int sum, place t_joinA) =
  split(t_splitA, ?t_writer1, ?t_splitB)
  &*& split(t_splitB, ?t_cat_split, ?t_reader1)

  &*& writestr_io(t_writer1, text, ?t_writer2)
  &*& cat_io(t_cat_split, _, ?t_cat_join)
  &*& readstr_io(t_reader1, length(text), _, sum, ?t_reader2)
  
  &*& join(t_cat_join, t_reader2, ?t_joinB)
  &*& join(t_writer2, t_joinB, t_joinA);


predicate system_invariant_inner(int family, struct system *system, list<int> buffer1_contents, list<int> buffer2_contents) =
  [1/2]progress(id_writer(family,system), ?progress_writer)
  &*& [1/2]progress(id_cat_read(family,system), ?progress_cat_read)
  &*& [1/2]progress(id_cat_write(family,system), ?progress_cat_write)
  &*& [1/2]progress(id_reader(family,system), ?progress_reader)
  
  &*& exists<pair<list<char>, list<int> > >(pair("cat_buffer", ?cat_buffer))
  
  // +-----------------------------------------------+
  // | write                                         |
  // +--------------------------------------+--------+       
  // | cat read                             | buffer1|
  // +---------------------+----------------+--------+       
  // | cat write           | (cat buffer)   |
  // +-----------+---------+----------------+       
  // | read      | buffer2 |
  // +-----------+---------+
  
  
  &*& progress_cat_write == append(progress_reader, buffer2_contents)
  &*& progress_cat_read == append(progress_cat_write, cat_buffer)
  &*& progress_writer == append(progress_cat_read, buffer1_contents);

predicate_ctor system_invariant(int family, struct system *system)() =
  system->ring_buffer1 |-> ?buffer1
  &*& ring_buffer(buffer1, _, ?buffer1_contents)
  &*& system->ring_buffer2 |-> ?buffer2
  &*& ring_buffer(buffer2, _, ?buffer2_contents)

  &*& system_invariant_inner(family, system, buffer1_contents, buffer2_contents);

predicate system(int family, struct system *system;) =
  system-> mutex|-> ?mutex
  &*& mutex(mutex, ((system_invariant)(family, system)))
  &*& system->cond_can_push1 |-> ?cond_can_push1
  &*& mutex_cond(cond_can_push1, mutex)
  &*& system->cond_can_push2 |-> ?cond_can_push2
  &*& mutex_cond(cond_can_push2, mutex)
  &*& system->cond_can_pop1 |-> ?cond_can_pop1
  &*& mutex_cond(cond_can_pop1, mutex)
  &*& system->cond_can_pop2 |-> ?cond_can_pop2
  &*& mutex_cond(cond_can_pop2, mutex)
  
  &*& malloc_block_system(system);
@*/

/*@
typedef lemma void can_write1(int c, place t1, place t2)();
  requires
    system_invariant_inner(?family, ?system, ?buffer1_contents, ?buffer2_contents)
    &*& token(t1, family, system);
  ensures
    system_invariant_inner(family, system, append(buffer1_contents, {c}), buffer2_contents)
    &*& token(t2, family, system);

typedef lemma void can_read2(int c, place t1, place t2)();
  requires
    system_invariant_inner(?family, ?system, ?buffer1_contents, ?buffer2_contents)
    &*& buffer2_contents != nil
    &*& exists<pair<list<char>, int > >(pair("ghost_cell_buf1", ?ghost_cell_buf1))
    &*& ghost_cell<list<int> >(ghost_cell_buf1, _)
    &*& ghost_cell<list<int> >(?ghost_cell_buf2, _)
    &*& prophecy(c, (read2_io_proph_invar)(t1, ghost_cell_buf1, ghost_cell_buf2))
    &*& token(t1, family, system);
  ensures
    system_invariant_inner(family, system, buffer1_contents, tail(buffer2_contents))
    &*& token(t2, family, system)
    &*& c == head(buffer2_contents);


// To create semi-anonymous lemmas using "produce_lemma_function_pointer_chunk(empty_lemma): some_lemma_typedef(....)(){...}"
lemma void empty_lemma()
  requires true;
  ensures true;
{
}
@*/

/** read from the second buffer. */
int read2(struct system *system)
//@ requires read2_io(?t1, ?x, ?t2) &*& token(t1, ?family, system) &*& [?f]system(family, system);
//@ ensures token(t2, family, system) &*& [f]system(family, system) &*& result == x;
{
  //@ open system(_, _);
  //@ assert [f]system->mutex |-> ?mutex;
  mutex_acquire(system->mutex);
  //@ open system_invariant(family,  system)();
   
  while (ring_buffer_is_empty(system->ring_buffer2))
  /*@ invariant
  
  // system:
  [f]system-> mutex|-> mutex
  //&*& [f]mutex(mutex, ((system_invariant)(family, system)))
  &*& [f]system->cond_can_push2 |-> ?cond_can_push2
  &*& [f]mutex_cond(cond_can_push2, mutex)
  &*& [f]system->cond_can_pop2 |-> ?cond_can_pop2
  &*& [f]mutex_cond(cond_can_pop2, mutex)
  
  // system_invariant:
  &*& system->ring_buffer1 |-> ?buffer1
  &*& ring_buffer(buffer1, _, ?buffer1_contents)
  &*& system->ring_buffer2 |-> ?buffer2
  &*& ring_buffer(buffer2, _, ?buffer2_contents)
  &*& system_invariant_inner(family, system, buffer1_contents, buffer2_contents)

  &*& mutex_held(mutex, (system_invariant)(family, system), currentThread, f);
  @*/
  {
    //@ close system_invariant(family, system)();
    mutex_cond_wait(system->cond_can_pop2, system->mutex);
    //@ open system_invariant(family, system)();
  }
  
  
  bool was_full = ring_buffer_is_full(system->ring_buffer2);
  
  int ret = ring_buffer_pop(system->ring_buffer2);
  
  if (was_full){
    mutex_cond_signal(system->cond_can_push2);
  }
  
  //@ open read2_io(t1, x, t2);
  //@ assert is_can_read2(?invar_updater, x, t1, t2);
  //@ invar_updater();
  //@ leak is_can_read2(_, _, _, _);

  //@ close system_invariant(family, system)();
  mutex_release(system->mutex);
  //@ close [f]system(family, system);
  
  return ret;
}

/** write to the first buffer. */
void write1(struct system *system, int x)
//@ requires write1_io(?t1, x, ?t2) &*& token(t1, ?family, system) &*& [?f]system(family, system);
//@ ensures token(t2, family, system) &*& [f]system(family, system);
{
  //@ open system(_, _);
  //@ assert [f]system->mutex |-> ?mutex;
  mutex_acquire(system->mutex);
  //@ open system_invariant(family,  system)();
   
  while (ring_buffer_is_full(system->ring_buffer1))
  /*@ invariant
  
  // system:
  [f]system-> mutex|-> mutex
  //&*& [f]mutex(mutex, ((system_invariant)(family, system)))
  &*& [f]system->cond_can_push1 |-> ?cond_can_push1
  &*& [f]mutex_cond(cond_can_push1, mutex)
  &*& [f]system->cond_can_pop1 |-> ?cond_can_pop1
  &*& [f]mutex_cond(cond_can_pop1, mutex)
  
  // system_invariant:
  &*& system->ring_buffer1 |-> ?buffer1
  &*& ring_buffer(buffer1, _, ?buffer1_contents)
  &*& system->ring_buffer2 |-> ?buffer2
  &*& ring_buffer(buffer2, _, ?buffer2_contents)
  &*& system_invariant_inner(family, system, buffer1_contents, buffer2_contents)

  &*& mutex_held(mutex, (system_invariant)(family, system), currentThread, f);
  @*/
  {
    //@ close system_invariant(family, system)();
    mutex_cond_wait(system->cond_can_push1, system->mutex);
    //@ open system_invariant(family, system)();
  }
  
  bool was_empty = ring_buffer_is_empty(system->ring_buffer1);
  
  ring_buffer_push(system->ring_buffer1, x);
  
  if (was_empty){
    mutex_cond_signal(system->cond_can_pop1);
  }
  //@ open write1_io(t1, x, t2);
  //@ assert is_can_write1(?invar_updater, x, t1, t2);
  //@ invar_updater();
  //@ leak is_can_write1(_, _, _, _);

  //@ close system_invariant(family, system)();
  mutex_release(system->mutex);
  //@ close [f]system(family, system);
}

/** writes to the first buffer. */
void writer(struct system *system)
//@ requires writestr_io(?t1, {1,2,3,4}, ?t2) &*& token(t1, ?family, system) &*& [?f]system(family, system);
//@ ensures token(t2, family, system) &*& [f]system(family, system);
{
  //@ open writestr_io(_, _, _);
  write1(system, 1);
  //@ open writestr_io(_, _, _);
  write1(system, 2);
  //@ open writestr_io(_, _, _);
  write1(system, 3);
  //@ open writestr_io(_, _, _);
  write1(system, 4);
  //@ open writestr_io(_, _, _);
}

/** reads from the first buffer and writes to the second buffer. */
void cat(struct system *system)
//@ requires cat_io(?t1, _, ?t2) &*& token(t1, ?family, system) &*& [?f]system(family, system);
//@ ensures token(t2, family, system) &*& [f]system(family, system);
{
  //@ assume(false); // TODO
}

/*@
fixpoint int plus(int a, int b) { return a + b; }
@*/

/** reads from the second buffer. */
int reader(struct system *system)
//@ requires readstr_io(?t1, 4, ?contents, ?sum, ?t2) &*& token(t1, ?family, system) &*& [?f]system(family, system);
//@ ensures token(t2, family, system) &*& [f]system(family, system) &*& result == sum;
{
  //@ open readstr_io(_, _, _, _, _);
  int r1 = read2(system);
  //@ open readstr_io(_, _, _, _, _);
  int r2 = read2(system);
  //@ open readstr_io(_, _, _, _, _);
  int r3 = read2(system);
  //@ open readstr_io(_, _, _, _, _);
  int r4 = read2(system);
  //@ open readstr_io(_, _, _, _, _);
  return r1 + r2 + r3 + r4;
  
  //@ switch (contents){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(contents)){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(tail(contents))){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(tail(tail(contents)))){ case nil: case cons(thehead, thetail): }
}

int do_system(struct system *system)
//@ requires token(?t1, ?family, system) &*& [?f]system(family, system) &*& system_io(t1, {1,2,3,4}, ?sum, ?t2);
//@ ensures token(t2, family, system) &*& [f]system(family, system) &*& result == sum;
{
  //@ open system_io(_, _, _, _);
  //@ assert split(t1, ?t_writer, ?t_to_split);
  //@ split(t1);
  //@ assert split(t_to_split, ?t_cat, ?t_reader);
  //@ split(t_to_split);
  
  // TODO Should be in threads...
  writer(system);
  //@ assert token(t_reader, family, system) &*& token(t_cat, family, system) &*& token(?t_writer2, family, system);
  cat(system);
  //@ assert token(t_reader, family, system) &*& token(t_writer2, family, system) &*& token(?t_cat2, family, system);
  int x = reader(system);
  //@ assert token(t_writer2, family, system) &*& token(t_cat2, family, system) &*& token(?t_reader2, family, system);
  //@ join(t_cat2);
  //@ join(t_writer2);
  
  return x;
}

/*@
lemma void close_write1(place tstart, int family, void *system, int val)
nonghost_callers_only
requires place_id(tstart) == id_writer(family, system);
ensures write1_io(tstart, val, place_io(tstart, val));
{
  place tstop = place_io(tstart, val);
  produce_lemma_function_pointer_chunk(empty_lemma) : can_write1(val, tstart, tstop)() {
    open system_invariant_inner(?fam, ?sys, ?buffer1_contents, ?buffer2_contents);
    open token(tstart, fam, sys);
    
    assert [1/2]progress(id_writer(fam,sys), ?progress_writer);
    assert [1/2]progress(id_cat_read(family,system), ?progress_cat_read);
    assert progress_writer == append(progress_cat_read, buffer1_contents);
    append_assoc(progress_cat_read, buffer1_contents, {val});
    assert append(progress_writer, {val}) == append(progress_cat_read, append(buffer1_contents,{val}));
    
    assert place_id(tstop) == id_writer(fam,sys);
    update_progress(id_writer(fam,sys), append(progress_writer, {val}));
    
    close system_invariant_inner(fam, sys, append(buffer1_contents, {val}), buffer2_contents);
    close token(tstop, fam, sys);
    call ();
  }{
    duplicate_lemma_function_pointer_chunk(can_write1);
  }
  close write1_io(tstart, val, tstop);
}
@*/

/*@
lemma place close_writer(int family, void *system, place tw_0)
nonghost_callers_only
requires
  place_id(tw_0) == id_writer(family, system)
  &*& place_progress(tw_0) == {}
  ;
ensures writestr_io(tw_0, {1,2,3,4}, ?tw_4) &*& place_id(tw_4) == place_id(tw_0) &*& result == tw_4
  &*& place_progress(tw_4) == {1,2,3,4} // easier to ensure here than to open writestr_io at caller-side.
  &*& place_parent1(result) == place_parent1(tw_0)
  &*& place_parent2(result) == place_parent2(tw_0)
  ;
{
  place tw_1 = place_io(tw_0, 1);
  place tw_2 = place_io(tw_1, 2);
  place tw_3 = place_io(tw_2, 3);
  place tw_4 = place_io(tw_3, 4);
  
  close_write1(tw_0, family, system, 1);
  close_write1(tw_1, family, system, 2);
  close_write1(tw_2, family, system, 3);
  close_write1(tw_3, family, system, 4);
  
  close writestr_io(tw_4, nil, tw_4);
  close writestr_io(tw_3, {4}, tw_4);
  close writestr_io(tw_2, {3,4}, tw_4);
  close writestr_io(tw_1, {2,3,4}, tw_4);
  close writestr_io(tw_0, {1,2,3,4}, tw_4);
  
  return tw_4;
}

lemma place close_cat_readstr_io(int family, void *system, place t1)
nonghost_callers_only
requires place_id(t1) == id_cat_read(family, system) &*& place_progress(t1) == {};
ensures readstr_io(t1, 4, ?readthis, ?sum, ?t2) &*& place_id(t2) == place_id(t1) &*& result == t2
  &*& place_parent1(result) == place_parent1(t1)
  &*& place_parent2(result) == place_parent2(t1)
  &*& place_progress(t2) == readthis
  &*& length(readthis) == 4;
{
  assume(false);
}

lemma place close_cat_writestr_io(int family, void *system, place tw_0, list<int> writethis)
nonghost_callers_only
requires
  place_id(tw_0) == id_cat_write(family, system)
  &*& place_progress(tw_0) == {}
  ;
ensures writestr_io(tw_0, writethis, ?tw_4) &*& place_id(tw_4) == place_id(tw_0) &*& result == tw_4
  &*& place_progress(tw_4) == writethis
  &*& place_parent1(result) == place_parent1(tw_0)
  &*& place_parent2(result) == place_parent2(tw_0)
  ;
{
  assume(false);
}



lemma place close_cat(int family, void *system, place t1)
nonghost_callers_only
requires
  place_id(t1) == id_cat_split(family, system)
  &*& [1/2]progress(id_cat_read(family,system), nil)
  &*& [1/2]progress(id_cat_write(family,system), nil)
  &*& [1/2]progress(id_cat_join(family,system), nil)
;
ensures
  cat_io(t1, ?readwrite, ?t2)
  &*& place_id(t2) == id_cat_join(family, system)
  &*& result == t2
  &*& place_parent1(place_parent1(t2)) == t1
  &*& place_parent1(place_parent2(t2)) == t1
  &*& length(place_progress(place_parent1(t2))) == 4
  &*& place_progress(place_parent1(t2)) == place_progress(place_parent2(t2))
//  &*& length(place_progress(place_parent2(t2))) == 4
  ;
{
  assert [1/2]progress(_, nil);
  close split(t1, ?t_cat_read1, ?t_cat_write1);
  place t_cat_read2 = close_cat_readstr_io(family, system, t_cat_read1);
  assert readstr_io(t_cat_read1, 4, ?readthis, _, _);
  place t_cat_write2 = close_cat_writestr_io(family, system, t_cat_write1, readthis);
  close join(t_cat_read2, t_cat_write2, ?t2);
  close cat_io(t1, readthis, t2);
  return t2;
}


lemma place close_read2(place tstart, int family, void *system)
nonghost_callers_only
requires place_id(tstart) == id_reader(family, system);
ensures read2_io(tstart, ?val, place_io(tstart, val)) &*& result == place_io(tstart, val) &*& exists(val);
{
  int ghost_cell_buf1 = create_ghost_cell<list<int> >(nil);
  close exists(pair("ghost_cell_buf1", ghost_cell_buf1));
  int ghost_cell_buf2 = create_ghost_cell<list<int> >(nil);
  int val = prophecy_create((read2_io_proph_invar)(tstart, ghost_cell_buf1, ghost_cell_buf2));
  place tstop = place_io(tstart, val);
  produce_lemma_function_pointer_chunk(empty_lemma) : can_read2(val, tstart, tstop)() {
    assert system_invariant_inner(?fam, ?sys, ?buffer1_contents_before, ?buffer2_contents_before);
    assert exists<pair<list<char>, int> >(pair("ghost_cell_buf1", ?ghost_cell_buf1_in_lemma));
    assert ghost_cell(ghost_cell_buf1_in_lemma, _) &*& ghost_cell(?ghost_cell_buf2_in_lemma, _);
    ghost_cell_mutate(ghost_cell_buf1_in_lemma, buffer1_contents_before);
    ghost_cell_mutate(ghost_cell_buf2_in_lemma, buffer2_contents_before);
    close read2_io_proph_invar(tstart, ghost_cell_buf1_in_lemma, ghost_cell_buf2_in_lemma)(head(buffer2_contents_before));
    prophecy_assign(val, head(buffer2_contents_before));
    open read2_io_proph_invar(tstart, ghost_cell_buf1_in_lemma, ghost_cell_buf2_in_lemma)(head(buffer2_contents_before));
    
    open system_invariant_inner(fam, sys, ?buffer1_contents, ?buffer2_contents);
    
    assert buffer1_contents == buffer1_contents_before; // thanks to the ghost cells.
    assert buffer2_contents == buffer2_contents_before;
    assert val == head(buffer2_contents);
    
    open token(tstart, _, _);
    assert [1/2]progress(id_reader(fam,sys), ?progress_reader);
    assert [1/2]progress(id_cat_write(family,system), ?progress_cat_write);
    assert progress_cat_write == append(progress_reader, buffer2_contents);
    
    append_assoc(progress_reader, {val}, tail(buffer2_contents));
    assert append(append(progress_reader, {val}), tail(buffer2_contents)) == append(progress_reader, append({val}, tail(buffer2_contents)));
    assert append({val}, tail(buffer2_contents)) == cons(val, tail(buffer2_contents));
    assert buffer2_contents != nil;
    assert val == head(buffer2_contents);
    switch(buffer2_contents){
      case nil:
      case cons(buffer2_contents_head, buffer2_contents_tail):
    }
    assert buffer2_contents == cons(val, tail(buffer2_contents));
    assert append(progress_reader, buffer2_contents) == append(append(progress_reader, {val}), tail(buffer2_contents));
    update_progress(id_reader(fam,sys), append(progress_reader, {val}));
    
    close system_invariant_inner(fam, sys, buffer1_contents_before, tail(buffer2_contents_before));
    close token(tstop, fam, sys);
    call ();
    leak exists(_);
    leak ghost_cell(_, _);
    leak ghost_cell(_, _);
  }{
    duplicate_lemma_function_pointer_chunk(can_read2);
  }
  close read2_io(tstart, val, tstop);
  return place_io(tstart, val);
}

lemma place close_reader(int family, void *system, place t1)
nonghost_callers_only
requires place_id(t1) == id_reader(family, system) &*& place_progress(t1) == {};
ensures readstr_io(t1, 4, ?readthis, ?sum, ?t2) &*& place_id(t2) == place_id(t1) &*& result == t2
  &*& place_parent1(result) == place_parent1(t1)
  &*& place_parent2(result) == place_parent2(t1)
  &*& length(place_progress(t2)) == 4
  &*& place_progress(t2) == readthis
;
{
  place tr_1 = close_read2(t1, family, system);
  leak exists(?c1);
  place tr_2 = close_read2(tr_1, family, system);
  leak exists(?c2);
  place tr_3 = close_read2(tr_2, family, system);
  leak exists(?c3);
  place tr_4 = close_read2(tr_3, family, system);
  leak exists(?c4);
  
  close readstr_io(tr_4, 0, nil, 0, tr_4);
  close readstr_io(tr_3, 1, {c4}, c4, tr_4);
  close readstr_io(tr_2, 2, {c3,c4}, c3+c4, tr_4);
  close readstr_io(tr_1, 3, {c2,c3,c4}, c2+c3+c4, tr_4);
  close readstr_io(t1  , 4, {c1,c2,c3,c4}, c1+c2+c3+c4, tr_4);
  return tr_4;
  
}

@*/

int main()
//@ requires true;
//@ ensures result == 10;
{
  struct system *system = malloc(sizeof(struct system));
  if (system == 0) abort(); 
  //@ int family = create_initial_progress(system);
  system->ring_buffer1 = ring_buffer_create(10);
  system->ring_buffer2 = ring_buffer_create(10);
  if (system->ring_buffer1 == 0 || system->ring_buffer2 == 0) abort();
  
  ///@ create_progress(id_splitA(family,system)   );
  //@ leak [1/2]progress(id_splitA(family,system), _);
  //@ create_progress(id_writer(family,system)   );
  //@ create_progress(id_splitB(family,system)   );
  //@ leak [1/2]progress(id_splitB(family,system), _);
  //@ create_progress(id_cat_split(family,system));
  //@ leak [1/2]progress(id_cat_split(family,system), _);
  //@ create_progress(id_cat_read(family,system) );
  ///@ leak [1/2]progress(id_cat_read(family,system), _);
  //@ create_progress(id_cat_write(family,system));
  ///@ leak [1/2]progress(id_cat_write(family,system), _);
  //@ create_progress(id_cat_join(family,system) );
  ///@ leak progress(id_cat_join(family,system), _);
  //@ create_progress(id_reader(family,system)   );
  //@ create_progress(id_joinB(family,system)    );
  //@ leak [1/2]progress(id_joinB(family,system), _);
  //@ create_progress(id_joinA(family,system)    );
  //@ leak [1/2]progress(id_joinA(family,system), _);
  //@ leak can_create_progress(_, _);


  //@ close exists<pair<list<char>, list<int> > >(pair("cat_buffer", {}));
  //@ close system_invariant_inner(family, system, nil, nil);
  
  //@ close system_invariant(family, system)();
  //@ close create_mutex_ghost_arg(system_invariant(family, system));
  system->mutex = create_mutex();
  
  //@ close create_mutex_cond_ghost_args(system->mutex);
  system->cond_can_push1 = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(system->mutex);
  system->cond_can_push2 = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(system->mutex);
  system->cond_can_pop1 = create_mutex_cond();
  //@ close create_mutex_cond_ghost_args(system->mutex);
  system->cond_can_pop2 = create_mutex_cond();
  
  //@ close system(family, system);
  
  //@ place t_splitA = place(id_splitA(family,system), no_place, no_place, nil);
  //@ close token(t_splitA, family, system);
  
  //@ close split(t_splitA, ?t_writer1, ?t_splitB);
  //@ close split(t_splitB, ?t_cat_split, ?t_reader1);
  //@ place t_writer2 = close_writer(family, system, t_writer1);
  
  //@ assert place_progress(t_writer1) == {};
  //@ assert place_progress(t_writer2) == {1,2,3,4};
  //@ place t_cat_join = close_cat(family, system, t_cat_split);
  //@ open cat_io(t_cat_split, ?cat_txt, t_cat_join);
  //@ close cat_io(t_cat_split, cat_txt, t_cat_join);
  //@ place t_reader2 = close_reader(family, system, t_reader1);
  
  //@ open readstr_io(t_reader1, 4, ?readthis, ?readstr_sum, t_reader2);
  //@ close readstr_io(t_reader1, 4, readthis, readstr_sum, t_reader2);
  
  //@ close join(t_cat_join, t_reader2, ?t_joinB);
  //@ close join(t_writer2, t_joinB, ?t_joinA);
  //@ close system_io(t_splitA, {1,2,3,4}, _ , t_joinA);
  
  int ret = do_system(system);
  
  //@ open system(_, _);
  mutex_acquire(system->mutex);
  //@ open system_invariant(family, system)();
  //@ open system_invariant_inner(family, system, ?buffer1_contents, ?buffer2_contents);
    
  //@ open [1]token(t_joinA, _, _);
  //@ assert place_id(t_joinA) == id_joinA(family, system);
  //@ open [1]token(t_writer2, _, _);
  //@ assert place_id(t_writer2) == id_writer(family, system);
  //@ open [1]token(t_joinB, _, _);
  //@ assert place_id(t_joinB) == id_joinB(family, system);
  //@ open [1]token(t_cat_join, _, _);
  //@ assert place_id(t_cat_join) == id_cat_join(family, system);
  //@ open [1]token(t_reader2, _, _);
  //@ assert place_id(t_reader2) == id_reader(family, system);
  
  //@ place t_cat_read2 = place_parent1(t_cat_join);
  //@ place t_cat_write2 = place_parent2(t_cat_join);
  //@ open [1]token(t_cat_read2, _, _);
  //@ open [1]token(t_cat_write2, _, _);
  //@ open [1]token(t_cat_split, _, _);
  //@ assert t_splitB == place_parent1(t_cat_split);
  //@ assert t_splitB == place_parent1(t_reader2);
  //@ open [1]token(t_splitB, _, _);
  //@ open [1]token(t_splitA, _, _);
    
  /*@ assert [1/2]progress(id_writer(family,system), ?progress_writer)
  &*& [1/2]progress(id_cat_read(family,system), ?progress_cat_read)
  &*& [1/2]progress(id_cat_write(family,system), ?progress_cat_write)
  &*& [1/2]progress(id_reader(family,system), ?progress_reader);
  @*/
  //@ assert progress_writer == {1,2,3,4};
  //@ assert length(progress_cat_read) == 4;
  //@ assert length(progress_cat_write) == 4;
  
  //@ assert progress_writer == append(progress_cat_read, buffer1_contents);
  //@ length_append(progress_cat_read, buffer1_contents);
  //@ assert length(buffer1_contents) == 0;
  //@ switch(buffer1_contents) { case nil: case cons(thehead, thetail): }
  //@ assert buffer1_contents == nil; // yay

  //@ assert progress_cat_read == progress_cat_write; // yay
  //@ assert progress_cat_read == progress_writer; // yay
  //@ assert progress_cat_write == append(progress_reader, buffer2_contents);
  //@ assert length(progress_cat_write) == length(progress_reader);
  //@ length_append(progress_reader, buffer2_contents);
  //@ switch(buffer2_contents) { case nil: case cons(thehead, theteail): }
  //@ assert buffer2_contents == nil; // yay
  
  //@ assert progress_writer == {1,2,3,4};
  //@ assert progress_reader == {1,2,3,4};
  
  //@ assert progress_reader == {1,2,3,4};
  //@ assert readthis == {1,2,3,4};
  //@ assert ret == fold_left(0, plus, progress_reader);
  
  // close everything
  //@ close [1]token(t_splitA, _, _);
  //@ close [1]token(t_splitB, _, _);
  //@ close [1]token(t_cat_split, _, _);
  //@ close [1]token(t_cat_write2, _, _);
  //@ close [1]token(t_cat_read2, _, _);
  //@ close [1]token(t_reader2, _, _);  
  //@ close [1]token(t_cat_join, _, _);
  //@ close [1]token(t_joinB, _, _);
  //@ close [1]token(t_writer2, _, _);
  //@ close [1]token(t_joinA, _, _);
  //@ close system_invariant_inner(family, system, buffer1_contents, buffer2_contents);
  //@ close system_invariant(family, system)();

  mutex_release(system->mutex);
  //@ close system(family, system);
  //@ leak system(_, _);
  //@ leak token(_, _, _);
  
  return ret;
  
  //@ leak [?f1]progress(_, _) &*& [?f2]progress(_, _) &*& [?f3]progress(_, _) &*& [?f4]progress(_, _) &*& [?f5]progress(_, _) &*& [?f6]progress(_, _);
}

