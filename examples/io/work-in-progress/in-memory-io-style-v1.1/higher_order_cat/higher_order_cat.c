/**
 * A program like cat, but the read and write are function pointers.
 *
 */

//@ #include "../io/io.gh"
#include "../readwrite_typedef_iostyle/readwrite_typedef_iostyle.h"

/*@
predicate reads_io(place t1, int count, list<int> contents, place t2) =
  count <= 0 ?
    t2 == t1
    &*& contents == nil
  :
    read_io(t1, ?c, ?t_read)
    &*& reads_io(t_read, count - 1, ?sub_contents, t2)
    &*& contents == cons(c, sub_contents)
;

predicate writes_io(place t1, list<int> contents, place t2) =
  contents == nil ?
    t2 == t1
  :
    write_io(t1, head(contents), ?t_write)
    &*& writes_io(t_write, tail(contents), t2)
;

predicate cat_io(place t1, int size, list<int> contents, place t2) =
  split(t1, ?t_read, ?t_write)
  &*& reads_io(t_read, size, contents, ?t_read_done)
  &*& writes_io(t_write, contents, ?t_write_done)
  &*& join(t_read_done, t_write_done, t2)
;
@*/

//@ predicate cat_ghost_arg(predicate(list<int> sigma) memrepr) = emp;
void cat(write_t *writer, read_t *reader, int size)
/*@ requires
  cat_io(?t1, size, ?contents, ?t2)
  &*& cat_ghost_arg(?memrepr)
  &*& token(?inst, t1)
  &*& [_]is_write_t(writer, memrepr)
  &*& [_]is_read_t(reader, memrepr)
  &*& size >= 0
  &*& all_tokens_invar(inst, ?sigma1)
  &*& memrepr(sigma1);
 @*/
/*@ ensures
  token(inst, t2)
  &*& all_tokens_invar(inst, ?sigma2)
  &*& memrepr(sigma2);
@*/
{
  //@ open cat_ghost_arg(memrepr);
  //@ open cat_io(_, _, _, _);
  int c1 = 0;
  int c2 = 0;
  int read_count = 0;
  //@ split();
  while (read_count < size)
    /*@ invariant
        reads_io(?t_read1, size - read_count, ?contents_todo, ?t_read2)
        &*& token(inst, t_read1)
        &*& writes_io(?t_write1, contents_todo, ?t_write2)
        &*& token(inst, t_write1)
        &*& join(t_read2, t_write2, t2)
        &*& [_]is_write_t(writer, memrepr)
        &*& [_]is_read_t(reader, memrepr)
        &*& memrepr(?sigma)
        &*& all_tokens_invar(inst, sigma)
      ;
    @*/
  {
    //@ open reads_io(_, _, _, _);
    //@ open writes_io(_, _, _);
    c1 = reader();
    writer(c1);
    read_count = read_count + 1;
  }
  //@ open reads_io(_, _, _, _);
  //@ open writes_io(_, _, _);
  //@ join();
}


