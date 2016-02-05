/**
 * Example of in-memory i/o-style verification.
 *
 * This example has a producer (which writes to a buffer),
 * a "cat" thread (that reads from that buffer and writes to
 * another buffer), and a consumer (that reads from the latter buffer).
 *
 */
 
#include "io.h"
#include "ids.h"
#include "prophecy.h"
//@ #include "gcf.gh"

#include <malloc.h>
#include <stdlib.h> // abort()
#include <threading.h>
//@ #include <ghost_cells.gh>
//@ #include "ghost_mutex.gh"

#include "queue.h"
#include "queue_string.h"


/*@
predicate cat_io(place t1, int family_buf1, int family_buf2, predicate() logic_invar, list<int> readwrite, place t2) =
  split(t1, ?t_cat_read1, ?t_cat_write1)
    &*& readstr_io(t_cat_read1, family_buf1, logic_invar, 4, readwrite, ?sum, ?t_cat_read2)
    &*& writestr_io(t_cat_write1, family_buf2, logic_invar, readwrite, ?t_cat_write2)
  &*& join(t_cat_read2, t_cat_write2, t2);

// logical invariant
predicate_ctor system_logic_invar(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write)() =
  [1/2]ghost_cell<list<int> >(family_buf1, ?buffer1_contents)
  &*& [1/2]ghost_cell<list<int> >(family_buf2, ?buffer2_contents)
  
  &*& [1/2]gcf_instance<id, progress_t>(family_io_read, id_writer(family_io_read), ?progress_reader)
  &*& [1/2]gcf_instance(family_io_cat, id_cat_read(family_io_cat), ?progress_cat_read)
  &*& [1/2]gcf_instance(family_io_cat, id_cat_write(family_io_cat), ?progress_cat_write)
  &*& [1/2]gcf_instance(family_io_write, id_reader(family_io_write), ?progress_writer)
  
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
@*/


/** reads from the first queue and writes to the second queue. */
void cat(struct queue *queue1, struct queue *queue2)
//@ requires cat_io(?t1, ?family_buf1, ?family_buf2, ?logic_invar, _, ?t2) &*& token(t1, ?family_io_cat) &*& [?fq1]queue(family_buf1, queue1) &*& [?fq2]queue(family_buf2, queue2) &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
//@ ensures token(t2, family_io_cat) &*& [fq1]queue(family_buf1, queue1) &*& [fq2]queue(family_buf2, queue2) &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
{
  //@ open cat_io(_, _, _, _, _, _);
  //@ split(t1);
  //@ open readstr_io(_, _, _, _, _, _, _);
  int c1 = queue_pop(queue1);
  //@ open readstr_io(_, _, _, _, _, _, _);
  int c2 = queue_pop(queue1);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue2, c1);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue2, c2);
  //@ open readstr_io(_, _, _, _, _, _, _);
  c1 = queue_pop(queue1);
  //@ open readstr_io(_, _, _, _, _, _, _);
  c2 = queue_pop(queue1);
  //@ open readstr_io(_, _, _, _, _, _, ?t_read_end);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue2, c1);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue2, c2);
  //@ open writestr_io(_, _, _, _, ?t_write_end);
  //@ join(t_read_end);  
}

/*@
predicate_ctor close_write1_pre(int c, int family_buf, list<int> buffer_contents, place t1, place t2, int family_io)() =
  [1/2]ghost_cell<list<int> >(family_buf, buffer_contents)
  &*& token(t1, family_io);
predicate_ctor close_write1_post(int c, int family_buf, list<int> buffer_contents, place t1, place t2, int family_io)() =
  [1/2]ghost_cell<list<int> >(family_buf, append(buffer_contents, {c}))
  &*& token(t2, family_io);

lemma void close_queue_push(place tstart, int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, int val)
nonghost_callers_only
requires place_id(tstart) == id_writer(family_io_write);
ensures write1_io(tstart, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), val, place_io(tstart, val));
{
  place tstop = place_io(tstart, val);
  predicate() logic_invar = system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  produce_lemma_function_pointer_chunk(empty_lemma) : can_queue_push(val, family_buf1, logic_invar, tstart, tstop)() {
    assert [1/2]ghost_cell<list<int> >(family_buf1, ?buffer_contents);
    assert token(_, ?family_io);
    predicate() pre = close_write1_pre(val, family_buf1, buffer_contents, tstart, tstop, family_io);
    predicate() post = close_write1_post(val, family_buf1, buffer_contents, tstart, tstop, family_io);

    close close_write1_pre(val, family_buf1, buffer_contents, tstart, tstop, family_io)(); // pre();
    produce_lemma_function_pointer_chunk(empty_lemma) : ghost_mutex_critical_section_t(logic_invar, pre, post)(){
      open system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
      open close_write1_pre(val, family_buf1, buffer_contents, tstart, tstop, family_io)();
      open token(tstart, _);
      
      assert [1/2]ghost_cell<list<int> >(family_buf1, ?buffer1_contents);
      assert [1/2]gcf_instance<id, progress_t>(family_io_write, id_writer(family_io_write), ?progress_writer);
      assert [1/2]gcf_instance(family_io_cat, id_cat_read(family_io_cat), ?progress_cat_read);
      append_assoc(progress_cat_read, buffer1_contents, {val});
      
      gcf_update(id_writer(family_io_write), append(progress_writer, {val}));
      ghost_cell_mutate<list<int> >(family_buf1, append(buffer1_contents,{val}));
      
      close system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
      close token(tstop, _);
      close close_write1_post(val, family_buf1, buffer_contents, tstart, tstop, family_io)();
      call();
    }
    {
      duplicate_lemma_function_pointer_chunk(ghost_mutex_critical_section_t);
    }
    assert [?fm]ghost_mutex(?ghost_mutex, logic_invar);
    ghost_mutex_use(ghost_mutex, pre, post);
    leak is_ghost_mutex_critical_section_t(_, _, _, _);
    open close_write1_post(val, family_buf1, buffer_contents, tstart, tstop, family_io)(); // post();
  
    call ();
  }{
    duplicate_lemma_function_pointer_chunk(can_queue_push);
  }
  close write1_io(tstart, family_buf1, logic_invar, val, place_io(tstart, val));
}
lemma place close_writer(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, place tw_0)
nonghost_callers_only
requires
  place_id(tw_0) == id_writer(family_io_write)
  &*& place_progress(tw_0) == {}
  ;
ensures writestr_io(tw_0, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), {1,2,3,4}, ?tw_4) &*& place_id(tw_4) == place_id(tw_0) &*& result == tw_4
  &*& place_progress(tw_4) == {1,2,3,4} // easier to ensure here than to open writestr_io at caller-side.
  &*& place_parent1(result) == place_parent1(tw_0)
  &*& place_parent2(result) == place_parent2(tw_0)
  ;
{
  place tw_1 = place_io(tw_0, 1);
  place tw_2 = place_io(tw_1, 2);
  place tw_3 = place_io(tw_2, 3);
  place tw_4 = place_io(tw_3, 4);
  
  close_queue_push(tw_0, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, 1);
  close_queue_push(tw_1, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, 2);
  close_queue_push(tw_2, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, 3);
  close_queue_push(tw_3, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, 4);
  
  close writestr_io(tw_4, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), nil, tw_4);
  close writestr_io(tw_3, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), {4}, tw_4);
  close writestr_io(tw_2, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), {3,4}, tw_4);
  close writestr_io(tw_1, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), {2,3,4}, tw_4);
  close writestr_io(tw_0, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), {1,2,3,4}, tw_4);
  
  return tw_4;
}


lemma place close_cat_readstr_io(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, place t1)
nonghost_callers_only
requires place_id(t1) == id_cat_read(family_io_cat) &*& place_progress(t1) == {};
ensures
  readstr_io(t1, family_buf1, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 4, ?readthis, ?sum, ?t2)
  &*& place_id(t2) == place_id(t1)
  &*& result == t2
  &*& place_parent1(result) == place_parent1(t1)
  &*& place_parent2(result) == place_parent2(t1)
  &*& place_progress(t2) == readthis
  &*& length(readthis) == 4;
{
  assume(false);
}



lemma place close_cat_writestr_io(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, place tw_0, list<int> writethis)
nonghost_callers_only
requires
  place_id(tw_0) == id_cat_write(family_io_cat)
  &*& place_progress(tw_0) == {}
  ;
ensures writestr_io(tw_0, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), writethis, ?tw_4) &*& place_id(tw_4) == place_id(tw_0) &*& result == tw_4
  &*& place_progress(tw_4) == writethis
  &*& place_parent1(result) == place_parent1(tw_0)
  &*& place_parent2(result) == place_parent2(tw_0)
  ;
{
  assume(false);
}


lemma place close_cat(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, place t1)
nonghost_callers_only
requires
  place_id(t1) == id_cat_split(family_io_cat)
  &*& [1/2]gcf_instance<id, progress_t>(family_io_cat, id_cat_read(family_io_cat), nil)
  &*& [1/2]gcf_instance<id, progress_t>(family_io_cat, id_cat_write(family_io_cat), nil)
  &*& [1/2]gcf_instance<id, progress_t>(family_io_cat, id_cat_join(family_io_cat), nil)
;
ensures
  cat_io(t1, family_buf1, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), ?readwrite, ?t2)
  &*& place_id(t2) == id_cat_join(family_io_cat)
  &*& result == t2
  &*& place_parent1(place_parent1(t2)) == t1
  &*& place_parent1(place_parent2(t2)) == t1
  &*& place_progress(place_parent1(t2)) == place_progress(place_parent2(t2))
  ;
{
  assert [1/2]gcf_instance(family_io_cat, _, nil);
  close split(t1, ?t_cat_read1, ?t_cat_write1);
  place t_cat_read2 = close_cat_readstr_io(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, t_cat_read1);
  assert readstr_io(t_cat_read1, family_buf1, _, 4, ?readthis, _, _);
  place t_cat_write2 = close_cat_writestr_io(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, t_cat_write1, readthis);
  close join(t_cat_read2, t_cat_write2, ?t2);
  close cat_io(t1, family_buf1, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), readthis, t2);
  return t2;
}

predicate_ctor close_read2_pre(int c, int family_buf, list<int> buffer_contents, place t1, place t2, int family_io, predicate() logic_invar)() =
  [1/2]ghost_cell<list<int> >(family_buf, buffer_contents)
  &*& buffer_contents != nil
  &*& c == head(buffer_contents)
  &*& token(t1, family_io);
predicate_ctor close_read2_post(int c, int family_buf, list<int> buffer_contents, place t1, place t2, int family_io, predicate() logic_invar)() =
  [1/2]ghost_cell<list<int> >(family_buf, tail(buffer_contents))
  &*& token(t2, family_io)
  &*& c == head(buffer_contents);
lemma place close_queue_pop(place tstart, int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write)
nonghost_callers_only
requires place_id(tstart) == id_reader(family_io_read);
ensures read2_io(tstart, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), ?val, place_io(tstart, val)) &*& result == place_io(tstart, val) &*& exists(val);
{
  int val = create_prophecy();
  place tstop = place_io(tstart, val);
  predicate() logic_invar = system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  produce_lemma_function_pointer_chunk(empty_lemma) : can_queue_pop(val, family_buf2, logic_invar, tstart, tstop)() {
    assert [1/2]ghost_cell<list<int> >(family_buf2, ?buffer_contents);
    assert token(_, ?family_io);
    predicate() pre = close_read2_pre(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar);
    predicate() post = close_read2_post(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar);
    
    close close_read2_pre(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar)(); // pre()
    produce_lemma_function_pointer_chunk(empty_lemma) : ghost_mutex_critical_section_t(logic_invar, pre, post)(){
      open close_read2_pre(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar)();
      assert system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
      
      assert [1/2]ghost_cell<list<int> >(family_buf2, ?buffer2_contents_before);
      
      open system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
      // Note that we do not have to prove that buffer1_contents remains the same during prophecy_assign, thanks to ghost cells.
      assert [1/2]ghost_cell<list<int> >(family_buf2, ?buffer2_contents);
      assert buffer2_contents == buffer2_contents_before;
      assert val == head(buffer2_contents);
    
      open token(tstart, _);
      assert [1/2]gcf_instance(family_io_read, id_reader(family_io_read), ?progress_reader);
      assert [1/2]gcf_instance(family_io_cat, id_cat_write(family_io_cat), ?progress_cat_write);
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
      gcf_update(id_reader(family_io_read), append(progress_reader, {val}));
      ghost_cell_mutate(family_buf2, tail(buffer2_contents));
    
      close system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
      close token(tstop, _);
      close close_read2_post(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar)();
      call ();
    }
    {
      duplicate_lemma_function_pointer_chunk(ghost_mutex_critical_section_t);
    }
    assert [?fm]ghost_mutex(?ghost_mutex, logic_invar);
    ghost_mutex_use(ghost_mutex, pre, post);
    leak is_ghost_mutex_critical_section_t(_, _, _, _);
    open close_read2_post(val, family_buf2, buffer_contents, tstart, tstop, family_io, logic_invar)(); // post();
    call();
  }{
    duplicate_lemma_function_pointer_chunk(can_queue_pop);
  }
  close read2_io(tstart, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), val, tstop);
  return place_io(tstart, val);
}

lemma place close_reader(int family_buf1, int family_buf2, int family_io_read, int family_io_cat, int family_io_write, place t1)
nonghost_callers_only
requires place_id(t1) == id_reader(family_io_read) &*& place_progress(t1) == {};
ensures readstr_io(t1, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 4, ?readthis, ?sum, ?t2) &*& place_id(t2) == place_id(t1) &*& result == t2
  &*& place_parent1(result) == place_parent1(t1)
  &*& place_parent2(result) == place_parent2(t1)
  &*& length(place_progress(t2)) == 4
  &*& place_progress(t2) == readthis
;
{
  place tr_1 = close_queue_pop(t1, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  leak exists(?c1);
  place tr_2 = close_queue_pop(tr_1, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  leak exists(?c2);
  place tr_3 = close_queue_pop(tr_2, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  leak exists(?c3);
  place tr_4 = close_queue_pop(tr_3, family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write);
  leak exists(?c4);
  
  close readstr_io(tr_4, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 0, nil, 0, tr_4);
  close readstr_io(tr_3, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 1, {c4}, c4, tr_4);
  close readstr_io(tr_2, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 2, {c3,c4}, c3+c4, tr_4);
  close readstr_io(tr_1, family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 3, {c2,c3,c4}, c2+c3+c4, tr_4);
  close readstr_io(t1  , family_buf2, system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write), 4, {c1,c2,c3,c4}, c1+c2+c3+c4, tr_4);
  return tr_4;
  
}

@*/

int main() //@ : main
//@ requires true;
//@ ensures result == 10;
{
  //@ int family_io_read = create_gcf();
  //@ create_gcf_instance<id, progress_t>(family_io_read, id_reader(family_io_read) ,{});
  //@ leak gcf(_, _);
  
  //@ int family_io_cat = create_gcf();
  //@ create_gcf_instance<id, progress_t>(family_io_cat, id_cat_split(family_io_cat),{});
  //@ leak [1/2]gcf_instance(family_io_cat,id_cat_split(family_io_cat), _);
  //@ create_gcf_instance<id, progress_t>(family_io_cat, id_cat_read(family_io_cat),{});
  //@ create_gcf_instance<id, progress_t>(family_io_cat, id_cat_write(family_io_cat),{});
  //@ create_gcf_instance<id, progress_t>(family_io_cat, id_cat_join(family_io_cat),{});
  //@ leak gcf(_, _);
  
  //@ int family_io_write = create_gcf();
  //@ create_gcf_instance<id, progress_t>(family_io_write, id_writer(family_io_write) ,{});
  //@ leak gcf(_, _);
  //@ close exists<pair<list<char>, list<int> > >(pair("cat_buffer", {}));
  
  struct queue *queue1 = create_queue(10);
  //@ assert queue(?family_buf1, _);
  struct queue *queue2 = create_queue(10);
  //@ assert queue(family_buf1, _) &*& queue(?family_buf2, _);
  //@ close system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
  //@ ghost_mutex ghost_mutex = create_ghost_mutex(system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write));
  
  //@ place t_writer1 = place(id_init(family_io_write), no_place, no_place, {});
  //@ place t_writer2 = close_writer(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, t_writer1);
  
  //@ assert place_progress(t_writer1) == {};
  //@ assert place_progress(t_writer2) == {1,2,3,4};
  //@ place t_cat_split = place(id_init(family_io_cat), no_place, no_place, {});
  //@ place t_cat_join = close_cat(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, t_cat_split);
  //@ open cat_io(t_cat_split, family_buf1, family_buf2, ?logic_invar, ?cat_txt, t_cat_join);
  //@ close cat_io(t_cat_split, family_buf1, family_buf2, logic_invar, cat_txt, t_cat_join);
  //@ place t_reader1 = place(id_init(family_io_read), no_place, no_place, {});
  //@ place t_reader2 = close_reader(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write, t_reader1);
  
  //@ open readstr_io(t_reader1, family_buf2, logic_invar, 4, ?readthis, ?readstr_sum, t_reader2);
  //@ close readstr_io(t_reader1, family_buf2, logic_invar, 4, readthis, readstr_sum, t_reader2);
  
  //@ close token(t_reader1, _);
  //@ close token(t_cat_split, _);
  //@ close token(t_writer1, _);
  
  writer(queue1);
  cat(queue1, queue2);
  int ret = reader(queue2);
  
  //@ ghost_mutex_dispose(ghost_mutex);
  //@ open system_logic_invar(family_buf1, family_buf2, family_io_read, family_io_cat, family_io_write)();
  
  struct ring_buffer *ring_buffer1 = queue_to_ring_buffer(queue1);
  struct ring_buffer *ring_buffer2 = queue_to_ring_buffer(queue2);
  
  //@ assert ring_buffer(ring_buffer1, _, ?buffer1_contents);
  //@ assert ring_buffer(ring_buffer2, _, ?buffer2_contents);  
  
  //@ open [1]token(t_writer2, _);
  //@ assert place_id(t_writer2) == id_writer(family_io_write);
  //@ open [1]token(t_cat_join, _);
  //@ assert place_id(t_cat_join) == id_cat_join(family_io_cat);
  //@ open [1]token(t_reader2, _);
  //@ assert place_id(t_reader2) == id_reader(family_io_read);
  
  //@ place t_cat_read2 = place_parent1(t_cat_join);
  //@ place t_cat_write2 = place_parent2(t_cat_join);
  //@ open [1]token(t_cat_read2, _);
  //@ open [1]token(t_cat_write2, _);
  //@ open [1]token(t_cat_split, _);
    
  /*@ assert [1/2]gcf_instance(family_io_write, id_writer(family_io_write), ?progress_writer)
  &*& [1/2]gcf_instance(family_io_cat, id_cat_read(family_io_cat), ?progress_cat_read)
  &*& [1/2]gcf_instance(family_io_cat, id_cat_write(family_io_cat), ?progress_cat_write)
  &*& [1/2]gcf_instance(family_io_read, id_reader(family_io_read), ?progress_reader);
  @*/
  //@ assert progress_writer == {1,2,3,4};
  
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
  
  // dispose everything.
  ring_buffer_dispose(ring_buffer1);
  ring_buffer_dispose(ring_buffer2);
  /*@ leak [?f1]gcf_instance(_, _, _) &*& [?f2]gcf_instance(_, _, _) &*& [?f3]gcf_instance(_, _, _) &*& [?f4]gcf_instance(_, _, _)
       &*& [?f5]gcf_instance(_, _, _) &*& [?f6]gcf_instance(_, _, _); @*/
  //@ leak ghost_cell(_, _) &*& ghost_cell(_, _);
  
  return ret;
}

#endif
