#ifndef READER_H
#define READER_H
//@ #include "io.gh"
#include "getchar.h"
//@ #include <listex.gh>

/*@
predicate reader_io<u>(int queue_id, place<u> t1, int n, list<int> read, place<u> t2) =
  n == 0 ?
    t2 == t1
    &*& read == nil
  :
    getchar_io(queue_id, t1, ?c, ?t_getchar)
    &*& reader_io(queue_id, t_getchar, n-1, ?subread, t2)
    &*& read == cons(c, subread);
@*/

//@ fixpoint int plus(int a, int b) { return a + b; }

/** Reads four ints and returns the sum. */
int reader/*@<u> @*/(struct queue *queue);
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& reader_io<u>(queue_id, ?t1, 4, ?read, ?t2)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue]queue(queue_id, queue)
  &*& token(t2)
  &*& result == fold_left(0, plus, read);
@*/

#endif
