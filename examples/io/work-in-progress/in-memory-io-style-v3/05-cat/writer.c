#include "writer.h"


/** Writes 1,2,3,4. */
void writer(struct queue *queue)
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& writer_io(queue_id, ?t1, {1,2,3,4}, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue]queue(queue_id, queue)
  &*& token(t2);
@*/
{
  //@ open writer_io(_, _, _, _);
  putchar(queue, 1);
  //@ open writer_io(_, _, _, _);
  putchar(queue, 2);
  //@ open writer_io(_, _, _, _);
  putchar(queue, 3);
  //@ open writer_io(_, _, _, _);
  putchar(queue, 4);
  //@ open writer_io(_, _, _, _);
}
