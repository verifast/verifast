/*
  A Buffer Program Synchronized Using Monitors: Verification of Deadlock-Freedom
*/

#include "stdlib.h"
//#include "monitors.h"
#include "queues11.h"
//@ #include "ghost_counters.gh"

struct buffer {
//   struct queue *q;
//   struct mutex *m;
//   struct condvar *v;
   //@ int gid;
};

void main()
  //@ requires true;// obs(nil);
  //@ ensures true;//obs(nil);
{
//  struct queue *q;// = create_queue();
    
  ///@ close create_mutex_ghost_args(0,nil);
  //struct mutex *m = create_mutex();
    
  struct buffer *b = malloc(sizeof(struct buffer));
  if (b==0)
    abort();    
//  b->q = q;
//  b->m = m;
    
//  //@ leak [_]b->v |-> _;
//  //@ leak [_]b->m |-> _;
  //@ leak [_]b->gid |-> _;
  ///@ leak b->q |-> _;
  ///@ leak umutex(_,empb,empb);
  ///@ leak queue1(q,0);
  //@ leak [_]malloc_block_buffer(_);


}
