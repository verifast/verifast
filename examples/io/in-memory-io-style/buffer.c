// Read documentation in syscall_memory.c.

#include <stdlib.h>
#include "buffer.h"
//@ #include "io/io.gh"
/**
 *
 * todo -> +--------+
 *         |        |
 *         |        |
 *         +--------+
 * done -> | done3  |
 *         | done2  |
 *         | ...    |
 *         +--------+
 */
struct iostate{
  char *todo;
  char *done;
  int size;
};

// Does not have to be global, but then you can support C APIs that
// require this (like putchar).
static struct iostate *global_iostate;

/*@
//inductive ioaction = ioaction_write(int encoding);
//inductive iostate = iostate(list<ioaction> actions);



predicate syscall_iostate(iostate state) =
  global_iostate |-> ?iostate_ptr
  &*& iostate_ptr->todo |-> ?todo
  &*& iostate_ptr->done |-> ?done
  &*& iostate_ptr->size |-> ?size
  &*& chars(todo, ?nb_todo, _)
  &*& chars(done, ?nb_done, ?done_chars)
  &*& nb_todo + nb_done == size
  &*& todo + nb_todo == done
  &*& done_chars == iostate_to_int_list(state)
 ;
@*/

void write(char c)
//@ requires syscall_iostate(?state);
//@ ensures syscall_iostate(iostate(cons(ioaction_write(c), iostate_to_list(state))));
{
  //@ open syscall_iostate(state);
  if (global_iostate->done == global_iostate->todo){
    abort(); // buffer full!
  }
  
  //@ assert global_iostate |-> ?iostate_ptr;
  //@ assert iostate_ptr->todo |-> ?todo;
  //@ assert chars(todo, ?nb_todo, _);
  //@ assert iostate_ptr->done |-> ?done;
  //@ assert chars(done, ?nb_done, _);
  
  //@ chars_split(todo, nb_todo - 1);
  
  //@ assert chars(todo, nb_todo - 1, _) &*& chars(todo + nb_todo - 1, nb_todo - (nb_todo - 1), _);
  
  //@ assert todo + nb_todo == done;
  
  global_iostate->done = global_iostate->done - 1;
  
  //@ open chars(todo + nb_todo - 1, _, _);
  
  *(global_iostate->done) = c;
  //@ close chars(done - 1, nb_done + 1, _);
  
  //@ close syscall_iostate(iostate(cons(ioaction_write(c), iostate_to_list(state))));
  
}

