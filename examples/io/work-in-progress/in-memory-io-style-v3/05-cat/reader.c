#include "reader.h"

/** Reads four ints and returns the sum. */
int reader(struct queue *queue)
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& reader_io(queue_id, ?t1, 4, ?read, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue]queue(queue_id, queue)
  &*& token(t2)
  &*& result == fold_left(0, plus, read);
@*/
{
  int sum = 0;
  //@ open reader_io(_, _, _, _, _);
  int c = getchar(queue);
  sum = sum + c;
  //@ open reader_io(_, _, _, _, _);
  c = getchar(queue);
  sum = sum + c;
  //@ open reader_io(_, _, _, _, _);
  c = getchar(queue);
  sum = sum + c;
  //@ open reader_io(_, _, _, _, _);
  c = getchar(queue);
  sum = sum + c;
  //@ open reader_io(_, _, _, _, _);
  return sum;
}