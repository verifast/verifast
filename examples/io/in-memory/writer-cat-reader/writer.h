#ifndef WRITER_H
#define WRITER_H
//@ #include "io.gh"
#include "putchar.h"

/*@
predicate writer_io<u>(int queue_id, place<u> t1, list<int> text, place<u> t2) =
  text == nil ?
    t2 == t1
  :
    putchar_io(queue_id, t1, head(text), ?t_putchar)
    &*& writer_io(queue_id, t_putchar, tail(text), t2);
@*/

/** Writes 1,2,3,4. */
void writer/*@<u> @*/(struct queue *queue);
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& writer_io<u>(queue_id, ?t1, {1,2,3,4}, ?t2)
  &*& token<u>(t1);
@*/
/*@ ensures
  [f_queue]queue(queue_id, queue)
  &*& token(t2);
@*/



#endif