/**
 * Provides writestring(queue, "a string")
 * functionality by doing multiple single-character write(queue, 'c') calls.
 *
 * Similar for reading, but includes a sum of what has been read.
 *
 * To reduce the size of this example, the values written and the amount of values read is fixed.
 * 
 */

#ifndef QUEUE_STRING_H
#define QUEUE_STRING_H

#include "io.h"
#include "queue.h"
//@ #include <listex.gh>

/*@
predicate writestr_io(place t1, int family1_buf, predicate() logic_invar, list<int> writethis, place t2) = 
  writethis == nil ?
    t1 == t2 // note: this will break choice, but we don't need it here.
  :
    write1_io(t1, family1_buf, logic_invar, head(writethis), ?tx)
    &*& writestr_io(tx, family1_buf, logic_invar, tail(writethis), t2);

fixpoint int plus(int a, int b) { return a + b; }
predicate readstr_io(place t1, int family2_buf, predicate() logic_invar, int count, list<int> readthis, int sum, place t2) =
  sum == fold_left(0, plus, readthis)
  &*& count <= 0 ?
    t2 == t1
    &*& sum == 0
    &*& readthis == nil
  : read2_io(t1, family2_buf, logic_invar, head(readthis), ?tx)
    &*& readstr_io(tx, family2_buf, logic_invar, count - 1, tail(readthis), ?tailsum, t2)
    &*& readthis != nil
    &*& sum == head(readthis) + tailsum;
@*/

void writer(struct queue *queue);
/*@ requires writestr_io(?t1, ?family_buf1, ?logic_invar, {1,2,3,4}, ?t2)
  &*& token(t1, ?family_io_write)
  &*& [?f]queue(family_buf1, queue)
  &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
@*/
/*@ ensures
  token(t2, family_io_write)
  &*& [f]queue(family_buf1, queue)
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
@*/

int reader(struct queue *queue);
/*@ requires readstr_io(?t1, ?family_buf2, ?logic_invar, 4, ?contents, ?sum, ?t2)
  &*& token(t1, ?family_io_read)
  &*& [?f]queue(family_buf2, queue)
  &*& [?fm]ghost_mutex(?ghost_mutex, logic_invar);
@*/
/*@ ensures token(t2, family_io_read)
  &*& [f]queue(family_buf2, queue)
  &*& result == sum
  &*& [fm]ghost_mutex(ghost_mutex, logic_invar);
@*/


#endif
