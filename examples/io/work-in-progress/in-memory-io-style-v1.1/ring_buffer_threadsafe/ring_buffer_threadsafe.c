#include "ring_buffer_threadsafe.h"

struct ring_buffer_threadsafe *ring_buffer_threadsafe_create()
//@ requires emp;
/*@ ensures
  result != 0 ?
    ring_buffer_threadsafe_shared(result)(?id_cell, unit)
  :
    emp;
@*/
{
  struct ring_buffer_threadsafe *buffer = malloc(sizeof(struct ring_buffer_threadsafe));
  if (buffer == 0){
    return 0;
  }
  
  struct ring_buffer *ring_buffer = ring_buffer_create(4096);
  if (ring_buffer == 0){
    free(buffer);
    return 0;
  }else{
    buffer->ring_buffer = ring_buffer;
    //@ int id_cell = create_ghost_cell<list<int> >({});
    //@ close ring_buffer_threadsafe(buffer, id_cell)();
    //@ close create_mutex_ghost_arg(ring_buffer_threadsafe(buffer, id_cell));
    struct mutex *mutex = create_mutex();
    buffer->mutex = mutex;
    //@ close ring_buffer_threadsafe_shared(buffer)(id_cell, unit);
    return buffer;
  }
}
