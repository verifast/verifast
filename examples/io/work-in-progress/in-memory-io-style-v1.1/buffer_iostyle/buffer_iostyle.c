#include "buffer_iostyle.h"

void write(struct buffer *buffer, int c) ///@ : write_t(buffer_memory)
/*@ requires
  write_io(?t1, c, ?t2)
  &*& token(?inst, t1)
  //&*& memrepr(?sigma)
  &*& buffer_memory(buffer, 1024)(?sigma) // TODO flexible buffer size?
  &*& all_tokens_invar(inst, sigma);
@*/
/*@ ensures
  token(inst, t2)
  //&*& memrepr(?sigma2)
  &*& buffer_memory(buffer, 1024)(?sigma2)
  &*& all_tokens_invar(inst, sigma2);
@*/
{
  //@ assume(false); // XXX
}
