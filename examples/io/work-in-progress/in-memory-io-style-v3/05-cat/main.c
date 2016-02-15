//@ #include "io.gh"
#include "reader.h"
#include "cat.h"
#include "writer.h"
#include <threading.h>
#include <stdlib.h> // abort()
//@ #include "ghost_mutex.gh"

/**
 * This invariant links the ghost cells representing the buffer's contents
 * with the ghost cell families instances representing the progresses of the
 * ghost IO threads.
 */
/*@
predicate_ctor invar(int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer)(;) =
  [1/2]ghost_cell<list<int> >(queue1_id, ?queue1_contents)
  &*& [1/2]ghost_cell<list<int> >(queue2_id, ?queue2_contents)
  
  &*& [1/2]gcf_instance<iot, progress_t >(family_reader, iot_init, ?progress_reader)
  &*& [1/2]gcf_instance(family_cat, iot_split_left(iot_init), ?progress_cat_read)
  &*& [1/2]gcf_instance(family_cat, iot_split_right(iot_init), ?progress_cat_write)
  &*& [1/2]gcf_instance(family_writer, iot_init, ?progress_writer)
  
  &*& ghost_cell<list<int> >(cat_buffer_id, ?cat_buffer)
  
  // +-----------------------------------------------+
  // | writer                                        |
  // +--------------------------------------+--------+
  // | cat read                             | queue1 |
  // +---------------------+----------------+--------+
  // | cat write           | (cat buffer)   |
  // +-----------+---------+----------------+
  // | reader    | queue2  |
  // +-----------+---------+
  
  &*& progress_cat_write == append(progress_reader, queue2_contents)
  &*& progress_cat_read == append(progress_cat_write, cat_buffer)
  &*& progress_writer == append(progress_cat_read, queue1_contents);
@*/

// TODO: move to writer.h, but verifast crashes on that.
/*@
predicate_family_instance thread_run_pre(writer_thread)(struct queue *queue, pair<int, place> queue_id_t2) =
  [1/2]queue(fst(queue_id_t2), queue) &*& writer_io(fst(queue_id_t2), ?t1, {1,2,3,4}, snd(queue_id_t2)) &*& token(t1);
predicate_family_instance thread_run_post(writer_thread)(struct queue *queue, pair<int, place> queue_id_t2) =
  [1/2]queue(fst(queue_id_t2), queue) &*& token(snd(queue_id_t2));
@*/

void writer_thread(struct queue *queue) //@ : thread_run_joinable
//@ requires thread_run_pre(writer_thread)(queue, ?info);
//@ ensures thread_run_post(writer_thread)(queue, info);
{
  //@ open thread_run_pre(writer_thread)(queue, ?x);
  writer(queue);
  //@ close thread_run_post(writer_thread)(queue, x);
}

struct cat_thread_info {
  struct queue *queue_from;
  struct queue *queue_to;
  //@ int queue_id_from;
  //@ int queue_id_to;
  //@ place t2;
};
/*@
predicate cat_thread_info(struct cat_thread_info *info; struct queue *queue_from,
    struct queue *queue_to, int queue_id_from, int queue_id_to, place t2) =
  info->queue_from |-> queue_from
  &*& info->queue_to |-> queue_to
  &*& info->queue_id_from |-> queue_id_from
  &*& info->queue_id_to |-> queue_id_to
  &*& info->t2 |-> t2;
predicate_family_instance thread_run_pre(cat_thread)(struct cat_thread_info *cat_thread_info, any info) =
  [1/2]cat_thread_info(cat_thread_info, ?queue_from, ?queue_to, ?queue_id_from, ?queue_id_to, ?t2)
  &*& [1/2]queue(queue_id_from, queue_from)
  &*& [1/2]queue(queue_id_to, queue_to)
  &*& cat_io(queue_id_from, queue_id_to, ?t1, _, t2)
  &*& token(t1);
predicate_family_instance thread_run_post(cat_thread)(struct cat_thread_info *cat_thread_info, any info) =
  [1/2]cat_thread_info(cat_thread_info, ?queue_from, ?queue_to, ?queue_id_from, ?queue_id_to, ?t2)
  &*& [1/2]queue(queue_id_from, queue_from)
  &*& [1/2]queue(queue_id_to, queue_to)
  &*& token(t2);
@*/
void cat_thread(struct cat_thread_info *cat_thread_info) //@ : thread_run_joinable
//@ requires thread_run_pre(cat_thread)(cat_thread_info, ?info);
//@ ensures thread_run_post(cat_thread)(cat_thread_info, info);
{
  //@ open thread_run_pre(cat_thread)(cat_thread_info, info);
  cat(cat_thread_info->queue_from, cat_thread_info->queue_to);
  //@ close thread_run_post(cat_thread)(cat_thread_info, info);
}


/*@
lemma place close_reader_getchar_io(
  int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer,
  place t1, ghost_mutex mutex
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_reader;
ensures getchar_io(queue2_id, t1, ?c, result)
  &*& result == place_upd_progress(t1, append(place_progress(t1), {c}));
{
  int c = create_prophecy();
  place t2 = place_upd_progress(t1, append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : getchar_invar_updatable(queue2_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer2_contents);
    open invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
      
    // Update ghost state:
    assert gcf_instance(family_reader, iot_init, ?progress_reader);
    gcf_update(family_reader, iot_init, append(progress_reader, {head(buffer2_contents)}));
    ghost_cell_mutate(queue2_id, tail(buffer2_contents));
      
    // Prove invariant still holds:
    append_assoc(progress_reader, {head(buffer2_contents)}, tail(buffer2_contents));
    switch(buffer2_contents){ case nil: case cons(head, tail): }
      
    close invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(getchar_invar_updatable);
  }
  close getchar_io(queue2_id, t1, c, t2);
  return t2;
}
@*/

/*@
lemma place close_cat_getchar_io(
  int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer,
  place t1, ghost_mutex mutex
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_split_left(iot_init)
  &*& place_family(t1) == family_cat;
ensures getchar_io(queue1_id, t1, ?c, result)
  &*& result == place_upd_progress(t1, append(place_progress(t1), {c}));
{
  int c = create_prophecy();
  place t2 = place_upd_progress(t1, append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : getchar_invar_updatable(queue1_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer1_contents);
    open invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    
    // Update ghost state:
    assert gcf_instance(family_cat, iot_split_left(iot_init), ?progress_cat_read);
    gcf_update(family_cat, iot_split_left(iot_init), append(progress_cat_read, {head(buffer1_contents)}));
    ghost_cell_mutate(queue1_id, tail(buffer1_contents));
    assert ghost_cell(cat_buffer_id, ?cat_buffer);
    ghost_cell_mutate(cat_buffer_id, append(cat_buffer, {head(buffer1_contents)}));
    
    // Prove invariant still holds:
    assert [?f]gcf_instance(family_cat, iot_split_right(iot_init), ?progress_cat_write);
    append_assoc(progress_cat_write, cat_buffer, {head(buffer1_contents)});
    append_assoc(progress_cat_read, {head(buffer1_contents)}, tail(buffer1_contents));
    switch(buffer1_contents){ case nil: case cons(head, tail): }
      
    close invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(getchar_invar_updatable);
  }
  close getchar_io(queue1_id, t1, c, t2);
  return t2;
}

lemma place close_cat_putchar_io(
  int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer,
  place t1, ghost_mutex mutex,
  int c
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_split_right(iot_init)
  &*& place_family(t1) == family_cat;
ensures putchar_io(queue2_id, t1, c, result)
  &*& result == place_upd_progress(t1, append(place_progress(t1), {c}));
{
  place t2 = place_upd_progress(t1, append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : putchar_invar_updatable(queue2_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer2_contents);
    open invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    
    // Update ghost state:
    assert gcf_instance(family_cat, iot_split_right(iot_init), ?progress_cat_write);
    gcf_update(family_cat, iot_split_right(iot_init), append(progress_cat_write, {c}));
    ghost_cell_mutate(queue2_id, append(buffer2_contents, {c}));
    assert ghost_cell(cat_buffer_id, ?cat_buffer);
    ghost_cell_mutate(cat_buffer_id, tail(cat_buffer));
    
    // Prove invariant still holds:
    assert [?f]gcf_instance(family_reader, iot_init, ?progress_reader);
    append_assoc(progress_reader, buffer2_contents, {c});
    
    assume (cat_buffer != nil); // TODO!
    assume (c == head(cat_buffer)); // TODO!
    append_assoc(progress_cat_write, {head(cat_buffer)}, tail(cat_buffer));
    
    switch(cat_buffer){ case nil: case cons(head, tail): }
    close invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(putchar_invar_updatable);
  }
  close putchar_io(queue2_id, t1, c, t2);
  return t2;
}

lemma place close_cat_io(
  int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer,
  place t1, ghost_mutex mutex
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_cat
  &*& [1/2]gcf_instance<iot, list<int> >(family_cat, iot_split_left(iot_init), {})
  &*& [1/2]gcf_instance<iot, list<int> >(family_cat, iot_split_right(iot_init), {})
  &*& [1/2]gcf_instance<iot, list<int> >(family_cat, iot_join(iot_split_left(iot_init), iot_split_right(iot_init)), {})
  ;
ensures cat_io(queue1_id, queue2_id, t1, ?cs, result)
  &*& place_family(result) == place_family(t1)
  &*& place_io_invar(result) == place_io_invar(t1)
  &*& place_famfract(result) == place_famfract(t1)
  &*& place_mutex(result) == place_mutex(t1) // TODO: introduce place_static for this things. We have these equalities at multiple places and it's hard to maintain.
  
  //&*& iot_fract(place_iot(result)) == iot_fract(place_iot(t1)) // TODO redux crashes on this
  
  &*& place_parent1(place_parent1(result)) == t1
  &*& place_parent1(place_parent2(result)) == t1
  &*& place_iot(result) == iot_join(iot_split_left(iot_init), iot_split_right(iot_init))
;
{
  close split(t1, ?t1_read, ?t1_write);
  
  place t2_read = close_cat_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t1_read, mutex);
  assert getchar_io(_, t1_read, ?c1, _);
  place t3_read = close_cat_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t2_read, mutex);
  assert getchar_io(_, t2_read, ?c2, _);
  place t4_read = close_cat_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t3_read, mutex);
  assert getchar_io(_, t3_read, ?c3, _);
  place t5_read = close_cat_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t4_read, mutex);
  assert getchar_io(_, t4_read, ?c4, _);
  close reader_io(queue1_id, t5_read, 0, _, t5_read);
  close reader_io(queue1_id, t4_read, 1, _, t5_read);
  close reader_io(queue1_id, t3_read, 2, _, t5_read);
  close reader_io(queue1_id, t2_read, 3, _, t5_read);
  close reader_io(queue1_id, t1_read, 4, _, t5_read);
  
  place t2_write = close_cat_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t1_write, mutex, c1);
  place t3_write = close_cat_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t2_write, mutex, c2);
  place t4_write = close_cat_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t3_write, mutex, c3);
  place t5_write = close_cat_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t4_write, mutex, c4);
  close writer_io(queue2_id, t5_write, {}, t5_write);
  close writer_io(queue2_id, t4_write, {c4}, t5_write);
  close writer_io(queue2_id, t3_write, {c3,c4}, t5_write);
  close writer_io(queue2_id, t2_write, {c2,c3,c4}, t5_write);
  close writer_io(queue2_id, t1_write, {c1,c2,c3,c4}, t5_write);
  
  close join(t5_read, t5_write, ?t2);
  close cat_io(queue1_id, queue2_id, t1, ?cs, t2);
  return t2;
}
@*/

/*@
lemma place close_writer_putchar_io(
  int queue1_id, int queue2_id, int cat_buffer_id, int family_reader, int family_cat, int family_writer,
  place t1, ghost_mutex mutex,
  int c
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_writer;
ensures putchar_io(queue1_id, t1, c, result)
  &*& result == place_upd_progress(t1, append(place_progress(t1), {c}));
{
  place t2 = place_upd_progress(t1, append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : putchar_invar_updatable(queue1_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer1_contents);
    open invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
      
    // Update ghost state:
    assert gcf_instance(family_writer, iot_init, ?progress_writer);
    gcf_update(family_writer, iot_init, append(progress_writer, {c}));
    ghost_cell_mutate(queue1_id, append(buffer1_contents, {c}));
      
    // Prove invariant still holds:
    //append_assoc(progress_reader, {head(buffer2_contents)}, tail(buffer2_contents));
    //switch(buffer2_contents){ case nil: case cons(head, tail): }
    assert [1/2]gcf_instance(family_cat, iot_split_left(iot_init), ?progress_cat_read);
    append_assoc(progress_cat_read, buffer1_contents, {c});
      
    close invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(putchar_invar_updatable);
  }
  close putchar_io(queue1_id, t1, c, t2);
  return t2;
}
@*/


int main() //@ : main
//@ requires true;
//@ ensures result == 10;
{
  struct queue *queue1 = create_queue(10);
  struct queue *queue2 = create_queue(10);
  //@ assert queue(?queue1_id, queue1) &*& queue(?queue2_id, queue2);
  //@ int family_reader = create_gcf<iot>();
  //@ create_gcf_instance<iot, list<int> >(family_reader, iot_init, nil);
  //@ int family_writer = create_gcf();
  //@ create_gcf_instance<iot, list<int> >(family_writer, iot_init, nil);
  //@ int family_cat = create_gcf();
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_init, nil);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_split_left(iot_init), nil);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_split_right(iot_init), nil);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_join(iot_split_left(iot_init), iot_split_right(iot_init)), nil);
  //@ int cat_buffer_id = create_ghost_cell<list<int> >(nil);
  
  //@ predicate(;) io_invar_full = invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer);
  //@ ghost_mutex mutex = create_ghost_mutex(io_invar_full);
    
  // close cat token
  //@ place t1_cat = place(iot_init, nil, place_none, place_none, io_invar_full, family_cat, 1/3, mutex);
  //@ close token_without_invar(t1_cat);
  //@ close io_invar_wrap(t1_cat);
  //@ close token(t1_cat);
  
  // close cat_io
  //@ place t2_cat = close_cat_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t1_cat, mutex);
  
  // start cat
  struct cat_thread_info *cat_info = malloc(sizeof(struct cat_thread_info));
  if (cat_info == 0) abort();
  cat_info->queue_from = queue1;
  cat_info->queue_to = queue2;
  //@ cat_info->queue_id_from = queue1_id;
  //@ cat_info->queue_id_to = queue2_id;
  //@ cat_info->t2 = t2_cat;
  //@ close cat_thread_info(cat_info, _, _, _, _, _);
  //@ close thread_run_pre(cat_thread)(cat_info, unit);
  struct thread *thread_cat = thread_start_joinable(cat_thread, cat_info);
    
  // close writer token
  //@ place t1_writer = place(iot_init, nil, place_none, place_none, io_invar_full, family_writer, 1/3, mutex);
  //@ close token(t1_writer);
  
  // close writer io
  //@ place t2_writer = close_writer_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t1_writer, mutex, 1);
  //@ place t3_writer = close_writer_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t2_writer, mutex, 2);
  //@ place t4_writer = close_writer_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t3_writer, mutex, 3);
  //@ place t5_writer = close_writer_putchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t4_writer, mutex, 4);
  //@ close writer_io(queue1_id, t5_writer, nil, t5_writer);
  //@ close writer_io(queue1_id, t4_writer, {4}, t5_writer);
  //@ close writer_io(queue1_id, t3_writer, {3,4}, t5_writer);
  //@ close writer_io(queue1_id, t2_writer, {2,3,4}, t5_writer);
  //@ close writer_io(queue1_id, t1_writer, {1,2,3,4}, t5_writer);
  
  // start writer
  //@ close thread_run_pre(writer_thread)(queue1, pair(queue1_id, t5_writer));
  struct thread *thread_writer = thread_start_joinable(writer_thread, queue1);
  
  // close reader token
  //@ place t1_reader = place(iot_init, nil, place_none, place_none, io_invar_full, family_reader, 1/3, mutex);
  //@ close token_without_invar(t1_reader);
  //@ close io_invar_wrap(t1_reader);
  //@ close token(t1_reader);
  
  // close reader io
  //@ place t2_reader = close_reader_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t1_reader, mutex);
  //@ place t3_reader = close_reader_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t2_reader, mutex);
  //@ place t4_reader = close_reader_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t3_reader, mutex);
  //@ place t5_reader = close_reader_getchar_io(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer, t4_reader, mutex);
  //@ close reader_io(queue2_id, t5_reader, 0, nil, t5_reader);
  //@ close reader_io(queue2_id, t4_reader, 1, _, t5_reader);
  //@ close reader_io(queue2_id, t3_reader, 2, _, t5_reader);
  //@ close reader_io(queue2_id, t2_reader, 3, _, t5_reader);
  //@ close reader_io(queue2_id, t1_reader, 4, _, t5_reader);
  
  // start reader
  int ret = reader(queue2);

  // wait for cat thread
  thread_join(thread_cat);
  
  // wait for writer thread
  thread_join(thread_writer);
  
  // Get our invariant back.
  //@ open token(t5_reader);
  //@ open thread_run_post(cat_thread)(cat_info, unit);
  //@ open token(_);
  //@ open thread_run_post(writer_thread)(queue1, pair(queue1_id, t5_writer));
  //@ open token(t5_writer);
  //@ open io_invar_wrap(_);
  //@ open io_invar_wrap(_);
  //@ open io_invar_wrap(_);
  //@ open cat_thread_info(_, _, _, _, _, _);
  //@ assert [?f]ghost_mutex(mutex, io_invar_full); 
  //@ assert f == iot_fract(place_iot(t2_reader))*1/3 + iot_fract(place_iot(t5_writer))*1/3 + iot_fract(place_iot(t2_cat))*1/3;
  //@ assert iot_fract(place_iot(t2_reader)) == 1;
  //@ assert iot_fract(place_iot(t5_writer)) == 1;
  ///@ assert iot_fract(place_iot(t2_cat)) == 1; // TODO should come out of close_cat_io's postcondition, but redux crashes (see close_cat_io lemma)
  //@ assume(iot_fract(place_iot(t2_cat)) == 1); // TODO: so we asume it for now.
  //@ ghost_mutex_dispose(mutex); // gives us the invariant.
  
  // Open things to obtain information about the fysical state.
  //@ open invar(queue1_id, queue2_id, cat_buffer_id, family_reader, family_cat, family_writer)();
  //@ open token_without_invar(t5_writer);
  //@ open token_without_invar(t5_reader);
  
  assert ret == 10;
  
  // Cleanup
  free(cat_info);
  struct ring_buffer *buffer1 = queue_to_ring_buffer(queue1);
  ring_buffer_dispose(buffer1);
  struct ring_buffer *buffer2 = queue_to_ring_buffer(queue2);
  ring_buffer_dispose(buffer2);
  
  // Ghost cleanup
  //@ leak gcf(family_reader, _) &*& gcf(family_cat, _) &*& gcf(family_writer, _);
  //@ leak gcf_instance(family_reader, iot_init, _) &*& gcf_instance(family_writer, iot_init, _);
  //@ open token_without_invar(t2_cat);
  //@ open token_without_invar(place_parent1(t2_cat));
  //@ open token_without_invar(place_parent2(t2_cat));
  //@ open token_without_invar(t1_cat);
  //@ leak gcf_instance(_, _, _) &*& gcf_instance(_, _, _) &*& [?f1]gcf_instance(_, _, _) &*& [?f2]gcf_instance(_, _, _) &*& [?f3]gcf_instance(_, _, _) &*& [?f4]gcf_instance(_, _, _);
  //@ leak ghost_cell(cat_buffer_id, _) &*& ghost_cell(_, _) &*& ghost_cell(_, _);
  
  return ret;
  
}

