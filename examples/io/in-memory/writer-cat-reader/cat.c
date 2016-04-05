#include "cat.h"

/**
 * Reads four numbers from queue_from, and write that to queue_to.
 * Buffering is allowed.
 */

void cat/*@<u> @*/(struct queue *queue_from, struct queue *queue_to)
/*@ requires
  [?f_queue_from]queue(?queue_id_from, queue_from)
  &*& [?f_queue_to]queue(?queue_id_to, queue_to)
  &*& cat_io<u>(queue_id_from, queue_id_to, ?t1, ?text, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue_from]queue(queue_id_from, queue_from)
  &*& [f_queue_to]queue(queue_id_to, queue_to)
  &*& token(t2);
@*/
{
  //@ open cat_io(_, _, _, _, _);
  //@ split(t1);
  int c1;
  int c2;
  //@ open reader_io(_, _, _, _, _);
  c1 = getchar(queue_from);
  //@ open reader_io(_, _, _, _, _);
  c2 = getchar(queue_from);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c1);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c2);
  //@ open reader_io(_, _, _, _, _);
  c1 = getchar(queue_from);
  //@ open reader_io(_, _, _, _, _);
  c2 = getchar(queue_from);
  //@ open reader_io(_, _, _, _, ?tr2);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c1);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c2);
  //@ open writer_io(_, _, _, _);
  //@ join(tr2); 
}
