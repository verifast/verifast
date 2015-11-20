#ifndef BUFFER_H
#define BUFFER_H

/**
 * ring_buffer_threadsafe.h - Example concurrent i/o in-memory representation
 * 
 */

//@ #include <ghost_cells.gh>
#include <threading.h>

// Ring buffer has been verified before, just reuse it.
#include "../../../../vstte2012/problem3/problem3.h"

struct ring_buffer_threadsafe{
  struct ring_buffer *ring_buffer;
  struct mutex *mutex;
};

/*@
predicate_ctor ring_buffer_threadsafe
  (struct ring_buffer_threadsafe *buffer, int id_cell)
  ()
=
  buffer->ring_buffer |-> ?ring_buffer
  &*& [1/2]ghost_cell(id_cell, ?sigma) 
  &*& ring_buffer(ring_buffer, 4096, sigma)
  &*& malloc_block_ring_buffer_threadsafe(buffer);
@*/

/*@
predicate_ctor ring_buffer_threadsafe_shared
  (struct ring_buffer_threadsafe *buffer)
  (int id_cell; unit u)
=
  [1/2]ghost_cell<list<int> >(id_cell, ?sigma)
  &*& buffer->mutex |-> ?mutex
  &*& mutex(mutex, ring_buffer_threadsafe(buffer, id_cell))
  &*& u == unit;
@*/

struct ring_buffer_threadsafe *ring_buffer_threadsafe_create();
//@ requires emp;
/*@ ensures
  result != 0 ?
    ring_buffer_threadsafe_shared(result)(?id_cell, unit)
  :
    emp;
@*/

#endif