#include "queue_string.h"

void writer(struct queue *queue)
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
{
  //@ open queue(_, _);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue, 1);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue, 2);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue, 3);
  //@ open writestr_io(_, _, _, _, _);
  queue_push(queue, 4);
  //@ open writestr_io(_, _, _, _, _);
  //@ close [f]queue(family_buf1, queue);
}

int reader(struct queue *queue)
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
{
  //@ open readstr_io(_, _, _, _, _, _, _);
  int r1 = queue_pop(queue);
  //@ open readstr_io(_, _, _, _, _, _, _);
  int r2 = queue_pop(queue);
  //@ open readstr_io(_, _, _, _, _, _, _);
  int r3 = queue_pop(queue);
  //@ open readstr_io(_, _, _, _, _, _, _);
  int r4 = queue_pop(queue);
  //@ open readstr_io(_, _, _, _, _, _, _);
  return r1 + r2 + r3 + r4;
  
  //@ switch (contents){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(contents)){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(tail(contents))){ case nil: case cons(thehead, thetail): }
  //@ switch (tail(tail(tail(contents)))){ case nil: case cons(thehead, thetail): }
}
