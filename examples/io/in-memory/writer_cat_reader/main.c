/**
 * This example is a program that has 3 threads and two buffers:
 *  - The write thread writes to buffer1
 *  - The cat thread reads from  buffer1 and writes to buffer2
 *  - The reader thread reads from buffer2 and calculates the sum of the values.
 *
 * This program does not perform any "classic" input/output, like reading from
 * keyboard or files, but is verified in an input/output verification style.
 *
 * The "main()" function does not have an input/output-style contract, but
 * ensures in its postcondition that its return-value will be a certain value.
 * The writer, cat, and reader thread use i/o style contracts and "main()"
 * closes the required precondition to be able to launch these threads.
 *
 * After the threads terminate, main opens the postcondition (which is i/o style)
 * and infers the value out of this.
 */

//@ #include "io.gh"
#include "reader.h"
#include "cat.h"
#include "writer.h"
#include <threading.h>
#include <stdlib.h> // abort()
//@ #include "ghost_mutex.gh"

/*@
inductive progress_t = progress(list<int> write_all, list<int> cat_prophecy, list<int> read_prophecy, list<int> thread_done);
fixpoint list<int> progress_write_all(progress_t progress){
  switch(progress){ case progress(write_all, cat_prophecy, read_prophecy, thread_done): return write_all; }
}
fixpoint list<int> progress_cat_prophecy(progress_t progress){
  switch(progress){ case progress(write_all, cat_prophecy, read_prophecy, thread_done): return cat_prophecy; }
}
fixpoint list<int> progress_read_prophecy(progress_t progress){
  switch(progress){ case progress(write_all, cat_prophecy, read_prophecy, thread_done): return read_prophecy; }
}
fixpoint list<int> progress_thread_done(progress_t progress){
  switch(progress){ case progress(write_all, cat_prophecy, read_prophecy, thread_done): return thread_done; }
}
fixpoint progress_t progress_append(progress_t progress, list<int> add_this){
  // avoid "switch", it needs an "assert myprogress==progress(_,_,...)" to prove
  //   progress_thread_done(progress_append(prog,x))==append(progress_thread_done(prog),x), which is confusing.
  return progress(progress_write_all(progress), progress_cat_prophecy(progress), progress_read_prophecy(progress), append(progress_thread_done(progress), add_this));
}
fixpoint bool progress_static_eq(progress_t progress1, progress_t progress2){
  return progress_write_all(progress1) == progress_write_all(progress2)
      && progress_cat_prophecy(progress1) == progress_cat_prophecy(progress2)
      && progress_read_prophecy(progress1) == progress_read_prophecy(progress2);
}
@*/


/**
 * This invariant links the ghost cells representing the buffer's contents
 * with the ghost cell families instances representing the progresses of the
 * ghost IO threads.
 */
/*@
predicate_ctor invar(int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer)() =
  [1/2]ghost_cell<list<int> >(queue1_id, ?queue1_contents)
  &*& [1/2]ghost_cell<list<int> >(queue2_id, ?queue2_contents)
  
  &*& [1/2]gcf_instance<iot, progress_t >(family_reader, iot_init, progress(?write_all, ?cat_prophecy, ?read_prophecy, ?reader))
  &*& [1/2]gcf_instance(family_cat, iot_split_left(iot_init),      progress( write_all,  cat_prophecy,  read_prophecy, ?cat_read))
  &*& [1/2]gcf_instance(family_cat, iot_split_right(iot_init),     progress( write_all,  cat_prophecy,  read_prophecy, ?cat_write))
  &*& [1/2]gcf_instance(family_writer, iot_init,                   progress( write_all,  cat_prophecy,  read_prophecy, ?writer))
  
  &*& exists<list<list<int> > >(cons(?writer_todo, cons(?cat_read_todo, cons(?cat_write_todo, cons(?reader_todo, nil)))))
  
  // +----------------------------------------------------+
  // | write_all                                          |
  // +-------------------------------+--------------------+ // (1)
  // | writer                        | writer_todo        |
  // +----------------------+--------+--------------------+ // (2)
  // | cat_read             | queue1 |
  // |                      +--------+
  // |                      |
  // |                      +-----------------------------+
  // |                      | cat_read_todo               |
  // +----------------------+-----------------------------+ // (3)
  // | cat_prophecy                                       |
  // +-----------------------------------+----------------+ // (4)
  // | cat_write                         | cat_write_todo |
  // +--------------------------+--------+----------------+ // (5)
  // | reader                   | queue2 |
  // |                          +--------+
  // |                          |
  // |                          +-------------------------+
  // |                          | reader_todo             |
  // +--------------------------+-------------------------+ // (6)
  // | read_prophecy                                      |
  // +----------------------------------------------------+
  
  &*& write_all     == append(writer,   writer_todo)     // (1)
  &*& writer        == append(cat_read, queue1_contents) // (2)
  &*& cat_prophecy  == append(cat_read, cat_read_todo)   // (3)
  &*& cat_prophecy  == append(cat_write,cat_write_todo)  // (4)
  &*& cat_write     == append(reader,   queue2_contents) // (5)
  &*& read_prophecy == append(reader,   reader_todo)     // (6)
;
@*/


/*@
predicate_family_instance thread_run_pre(writer_thread)(struct queue *queue, pair<int, place<progress_t > > queue_id_t2) =
  [1/2]queue(fst(queue_id_t2), queue) &*& writer_io(fst(queue_id_t2), ?t1, {1,2,3,4}, snd(queue_id_t2)) &*& token(t1);
predicate_family_instance thread_run_post(writer_thread)(struct queue *queue, pair<int, place<progress_t > > queue_id_t2) =
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
  //@ place<progress_t> t2;
};
/*@
predicate cat_thread_info(struct cat_thread_info *info; struct queue *queue_from,
    struct queue *queue_to, int queue_id_from, int queue_id_to, place<progress_t > t2) =
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
lemma void append_eq<t>(list<t> x, list<t> y, list<t> z)
  requires append(x, y) == append(x, z);
  ensures y == z;
{
  switch(x){
    case nil:
    case cons(head, tail):
      append_eq(tail, y, z);
  }
}
@*/

/*@
lemma place<progress_t> close_reader_getchar_io(
  int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer,
  place<progress_t> t1, ghost_mutex mutex,
  int c, list<int> todo
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_reader
  &*& prophecy(c)
  &*& head(todo) == c
  &*& todo != nil
  &*& progress_read_prophecy(place_progress(t1)) == append(progress_thread_done(place_progress(t1)), todo);
ensures getchar_io(queue2_id, t1, c, result)
  &*& result == place_upd_progress(t1, progress_append(place_progress(t1), {c}));
{
  place<progress_t> t2 = place_upd_progress(t1, progress_append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : getchar_invar_updatable<progress_t>(queue2_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?queue2_contents);
    open invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
      
    // Update ghost state:
    assert gcf_instance(family_reader, iot_init, ?progress_reader);
    gcf_update(family_reader, iot_init, progress_append(progress_reader, {head(queue2_contents)}));
    ghost_cell_mutate(queue2_id, tail(queue2_contents));
    open exists<list<list<int> > >(cons(?writer_todo, cons(?cat_read_todo, cons(?cat_write_todo, cons(?reader_todo, nil)))));
    close exists(cons(writer_todo, cons(cat_read_todo, cons(cat_write_todo, cons(tail(reader_todo), nil)))));
    
    // Prove invariant still holds:
    assert progress_reader == progress(?write_all, ?cat_prophecy, ?read_prophecy, ?reader);
    append_assoc(reader, {c}, tail(queue2_contents));
    switch(queue2_contents){ case nil: case cons(head, tail): }
    
    append_eq(reader, reader_todo, todo);
    switch(todo){ case nil: case cons(head, tail): }
    append_assoc(reader, {c}, tail(reader_todo));
    
    close invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
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
lemma place<progress_t> close_cat_getchar_io(
  int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer,
  place<progress_t> t1, ghost_mutex mutex,
  int c, list<int> todo
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_split_left(iot_init)
  &*& place_family(t1) == family_cat
  &*& prophecy(c)
  &*& head(todo) == c
  &*& todo != nil
  &*& progress_cat_prophecy(place_progress(t1)) == append(progress_thread_done(place_progress(t1)), todo);
ensures getchar_io(queue1_id, t1, c, result)
  &*& result == place_upd_progress(t1, progress_append(place_progress(t1), {c}));
{
  place<progress_t> t2 = place_upd_progress(t1, progress_append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : getchar_invar_updatable<progress_t>(queue1_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?queue1_contents);
    open invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
    
    // Update ghost state:
    assert gcf_instance(family_cat, iot_split_left(iot_init), ?progress_cat_read);
    gcf_update(family_cat, iot_split_left(iot_init), progress_append(progress_cat_read, {c}));
    ghost_cell_mutate(queue1_id, tail(queue1_contents));
    open exists<list<list<int> > >(cons(?writer_todo, cons(?cat_read_todo, cons(?cat_write_todo, cons(?reader_todo, nil)))));
    close exists(cons(writer_todo, cons(tail(cat_read_todo), cons(cat_write_todo, cons(reader_todo, nil)))));
    
    // Prove invariant still holds:
    assert progress_cat_read == progress(?write_all, ?cat_prophecy, ?read_prophecy, ?cat_read);
    assert [?f]gcf_instance(family_cat, iot_split_right(iot_init), ?progress_cat_write);
    append_eq(cat_read, cat_read_todo, todo);
    switch(todo){ case nil: case cons(head, tail): }
    append_assoc(cat_read, {c}, tail(cat_read_todo));
    append_assoc(progress_thread_done(progress_cat_read), {c}, tail(queue1_contents));
    switch(queue1_contents){ case nil: case cons(head, tail): }
      
    close invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(getchar_invar_updatable);
  }
  close getchar_io(queue1_id, t1, c, t2);
  return t2;
}

lemma place<progress_t> close_cat_putchar_io(
  int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer,
  place<progress_t> t1, ghost_mutex mutex,
  int c, list<int> todo
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_split_right(iot_init)
  &*& place_family(t1) == family_cat
  &*& head(todo) == c
  &*& todo != nil
  &*& progress_cat_prophecy(place_progress(t1)) == append(progress_thread_done(place_progress(t1)), todo);
ensures putchar_io(queue2_id, t1, c, result)
  &*& result == place_upd_progress(t1, progress_append(place_progress(t1), {c}));
{
  place<progress_t> t2 = place_upd_progress(t1, progress_append(place_progress(t1), {c}));
  
  produce_lemma_function_pointer_chunk(empty_lemma) : putchar_invar_updatable<progress_t>(queue2_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer2_contents);
    open invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
    
    // Update ghost state:
    assert gcf_instance(family_cat, iot_split_right(iot_init), ?progress_cat_write);
    gcf_update(family_cat, iot_split_right(iot_init), progress_append(progress_cat_write, {c}));
    ghost_cell_mutate(queue2_id, append(buffer2_contents, {c}));
    open exists<list<list<int> > >(cons(?writer_todo, cons(?cat_read_todo, cons(?cat_write_todo, cons(?reader_todo, nil)))));
    close exists(cons(writer_todo, cons(cat_read_todo, cons(tail(cat_write_todo), cons(reader_todo, nil)))));
    
    // Prove invariant still holds:
    assert [?f]gcf_instance(family_reader, iot_init, ?progress_reader);
    append_assoc(progress_thread_done(progress_reader), buffer2_contents, {c});
    assert progress_cat_write == progress(?write_all, ?cat_prophecy, ?read_prophecy, ?cat_write);
    append_eq(cat_write, cat_write_todo, todo);
    append_assoc(cat_write, {c}, tail(todo));
    
    switch(todo){ case nil: case cons(head, tail): }
    close invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(putchar_invar_updatable);
  }
  close putchar_io(queue2_id, t1, c, t2);
  return t2;
}


lemma place<progress_t> close_cat_io(
  int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer,
  place<progress_t> t1, ghost_mutex mutex
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_cat
  &*& place_init_progress(t1) == progress({1,2,3,4}, ?cat_prophecy, _, {})
  &*& cat_prophecy == cons(?c1, cons(?c2, cons(?c3, cons(?c4, nil))))
  &*& prophecy(c1) &*& prophecy(c2) &*& prophecy(c3) &*& prophecy(c4)
  &*& [1/2]gcf_instance<iot, progress_t >(family_cat, iot_split_left(iot_init), place_init_progress(t1))
  &*& [1/2]gcf_instance<iot, progress_t >(family_cat, iot_split_right(iot_init), place_init_progress(t1))
  &*& [1/2]gcf_instance<iot, progress_t >(family_cat, iot_join(iot_split_left(iot_init), iot_split_right(iot_init)), place_init_progress(t1))
  ;
ensures cat_io(queue1_id, queue2_id, t1, cat_prophecy, result)
  &*& true==place_static_eq(result, t1)
  
  &*& place_parent1(place_parent1(result)) == t1
  &*& place_parent1(place_parent2(result)) == t1
  &*& place_iot(result) == iot_join(iot_split_left(iot_init), iot_split_right(iot_init))
  
  &*& progress_thread_done(place_progress(place_parent1(result))) == cat_prophecy
  &*& progress_thread_done(place_progress(place_parent2(result))) == cat_prophecy
;
{
  close split(t1, ?t1_read, ?t1_write);
   
  place<progress_t> t2_read = close_cat_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t1_read, mutex, c1, {c1, c2, c3, c4});
  place<progress_t> t3_read = close_cat_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t2_read, mutex, c2, {c2, c3, c4});
  place<progress_t> t4_read = close_cat_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t3_read, mutex, c3, {c3, c4});
  place<progress_t> t5_read = close_cat_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t4_read, mutex, c4, {c4});
  close reader_io(queue1_id, t5_read, 0, _, t5_read);
  close reader_io(queue1_id, t4_read, 1, _, t5_read);
  close reader_io(queue1_id, t3_read, 2, _, t5_read);
  close reader_io(queue1_id, t2_read, 3, _, t5_read);
  close reader_io(queue1_id, t1_read, 4, _, t5_read);
  
  place<progress_t> t2_write = close_cat_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t1_write, mutex, c1, {c1, c2, c3, c4});
  place<progress_t> t3_write = close_cat_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t2_write, mutex, c2, {c2, c3, c4});
  place<progress_t> t4_write = close_cat_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t3_write, mutex, c3, {c3, c4});
  place<progress_t> t5_write = close_cat_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t4_write, mutex, c4, {c4});
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
lemma place<progress_t> close_writer_putchar_io(
  int queue1_id, int queue2_id, int family_reader, int family_cat, int family_writer,
  place<progress_t> t1, ghost_mutex mutex,
  int c, list<int> todo
)
nonghost_callers_only
requires place_io_invar(t1) == invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)
  &*& place_iot(t1) == iot_init
  &*& place_family(t1) == family_writer
  &*& c == head(todo)
  &*& todo != nil
  &*& progress_write_all(place_progress(t1)) == append(progress_thread_done(place_progress(t1)), todo);
ensures putchar_io(queue1_id, t1, c, result)
  &*& result == place_upd_progress(t1, progress_append(place_progress(t1), {c}));
{
  place<progress_t> t2 = place_upd_progress(t1, progress_append(place_progress(t1), {c}));

  produce_lemma_function_pointer_chunk(empty_lemma) : putchar_invar_updatable<progress_t>(queue1_id, t1, c, t2)() {
    assert [1/2]ghost_cell(_, ?buffer1_contents);
    open invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
      
    // Update ghost state:
    assert gcf_instance(family_writer, iot_init, ?progress_writer);
    gcf_update(family_writer, iot_init, progress_append(progress_writer, {c}));
    ghost_cell_mutate(queue1_id, append(buffer1_contents, {c}));
    open exists<list<list<int> > >(cons(?writer_todo, cons(?cat_read_todo, cons(?cat_write_todo, cons(?reader_todo, nil)))));
    close exists(cons(tail(writer_todo), cons(cat_read_todo, cons(cat_write_todo, cons(reader_todo, nil)))));
      
    // Prove invariant still holds:
    assert [1/2]gcf_instance(family_cat, iot_split_left(iot_init), ?progress_cat_read);
    assert progress_writer == progress(?write_all, ?cat_prophecy, ?read_prophecy, ?writer);
    append_assoc(progress_thread_done(progress_cat_read), buffer1_contents, {c});
    append_eq(writer, todo, writer_todo);
    append_assoc(writer, {c}, tail(writer_todo));
    switch(todo){ case nil: case cons(h,t): }
    
    close invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
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
  // Define init_progress
  //@ list<int> writer_todo = {1, 2, 3, 4};
  //@ int c1_c = create_prophecy();
  //@ int c2_c = create_prophecy();
  //@ int c3_c = create_prophecy();
  //@ int c4_c = create_prophecy();
  //@ list<int> cat_prophecy = {c1_c, c2_c, c3_c, c4_c};
  //@ int c1_r = create_prophecy();
  //@ int c2_r = create_prophecy();
  //@ int c3_r = create_prophecy();
  //@ int c4_r = create_prophecy();
  //@ list<int> read_prophecy = {c1_r, c2_r, c3_r, c4_r};
  //@ progress_t init_progress = progress(writer_todo, cat_prophecy, read_prophecy, nil);

  // Create queues.
  struct queue *queue1 = create_queue(10);
  struct queue *queue2 = create_queue(10);
  //@ assert queue(?queue1_id, queue1) &*& queue(?queue2_id, queue2);
  
  // Close invar
  //@ int family_reader = create_gcf<iot>();
  //@ create_gcf_instance<iot, progress_t >(family_reader, iot_init, init_progress);
  //@ int family_writer = create_gcf();
  //@ create_gcf_instance<iot, progress_t >(family_writer, iot_init, init_progress);
  //@ int family_cat = create_gcf();
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_init, init_progress);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_split_left(iot_init), init_progress);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_split_right(iot_init), init_progress);
  //@ create_gcf_instance<iot, progress_t >(family_cat, iot_join(iot_split_left(iot_init), iot_split_right(iot_init)), init_progress);
  //@ close exists<list<list<int > > >({writer_todo, cat_prophecy, cat_prophecy, read_prophecy});
  //@ predicate() io_invar_full = invar(queue1_id, queue2_id, family_reader, family_cat, family_writer);
  //@ assert append({}, {}) == {}; // Redux needs a hint...
  //@ close invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
  
  //@ ghost_mutex mutex = create_ghost_mutex(io_invar_full);
    
  // close cat token
  //@ place<progress_t> t1_cat = place<progress_t>(iot_init, init_progress, place_none, place_none, io_invar_full, family_cat, 1/3, mutex, init_progress);
  //@ close token_without_invar(t1_cat);
  //@ close io_invar_wrap(t1_cat);
  //@ close token(t1_cat);
  
  // close cat_io
  //@ place<progress_t> t2_cat = close_cat_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t1_cat, mutex);
  
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
  //@ place<progress_t> t1_writer = place<progress_t>(iot_init, init_progress, place_none, place_none, io_invar_full, family_writer, 1/3, mutex, init_progress);
  //@ close token(t1_writer);
  
  // close writer io
  //@ place<progress_t> t2_writer = close_writer_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t1_writer, mutex, 1, {1,2,3,4});
  //@ place<progress_t> t3_writer = close_writer_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t2_writer, mutex, 2, {2,3,4});
  //@ place<progress_t> t4_writer = close_writer_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t3_writer, mutex, 3, {3,4});
  //@ place<progress_t> t5_writer = close_writer_putchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t4_writer, mutex, 4, {4});
  //@ close writer_io(queue1_id, t5_writer, nil, t5_writer);
  //@ close writer_io(queue1_id, t4_writer, {4}, t5_writer);
  //@ close writer_io(queue1_id, t3_writer, {3,4}, t5_writer);
  //@ close writer_io(queue1_id, t2_writer, {2,3,4}, t5_writer);
  //@ close writer_io(queue1_id, t1_writer, {1,2,3,4}, t5_writer);
  
  // start writer
  //@ close thread_run_pre(writer_thread)(queue1, pair(queue1_id, t5_writer));
  struct thread *thread_writer = thread_start_joinable(writer_thread, queue1);
  
  // close reader token
  //@ place<progress_t> t1_reader = place(iot_init, init_progress, place_none, place_none, io_invar_full, family_reader, 1/3, mutex, init_progress);
  //@ close token_without_invar(t1_reader);
  //@ close io_invar_wrap(t1_reader);
  //@ close token(t1_reader);
  
  // close reader io
  //@ place<progress_t> t2_reader = close_reader_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t1_reader, mutex, c1_r, {c1_r, c2_r, c3_r, c4_r});
  //@ place<progress_t> t3_reader = close_reader_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t2_reader, mutex, c2_r, {c2_r, c3_r, c4_r});
  //@ place<progress_t> t4_reader = close_reader_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t3_reader, mutex, c3_r, {c3_r, c4_r});
  //@ place<progress_t> t5_reader = close_reader_getchar_io(queue1_id, queue2_id, family_reader, family_cat, family_writer, t4_reader, mutex, c4_r, {c4_r});
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
  
  // Get our invariant back
  //@ open token(t5_reader);
  //@ open thread_run_post(cat_thread)(cat_info, unit);
  //@ open token(t2_cat);
  //@ open thread_run_post(writer_thread)(queue1, pair(queue1_id, t5_writer));
  //@ open token(t5_writer);
  //@ open io_invar_wrap(_);
  //@ open io_invar_wrap(_);
  //@ open io_invar_wrap(_);
  //@ open cat_thread_info(_, _, _, _, _, _);
  //@ ghost_mutex_dispose(mutex); // gives us the invariant.
  
  // Open predicates to obtain information about the fysical state
  //@ open invar(queue1_id, queue2_id, family_reader, family_cat, family_writer)();
  //@ open token_without_invar(t5_writer);
  //@ open token_without_invar(t5_reader);
  //@ open token_without_invar(t2_cat);
  //@ open token_without_invar(place_parent1(t2_cat));
  //@ open token_without_invar(place_parent2(t2_cat));
  //@ open token_without_invar(place_parent1(place_parent1(t2_cat)));
  
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
  //@ leak exists(_) &*& ghost_cell(_, _) &*& ghost_cell(_, _);
  
  return ret;
  
}

