#ifndef BUFFER_H
#define BUFFER_H

//@ #include "../io/io.gh"

#include "../readwrite_typedef_iostyle/readwrite_typedef_iostyle.h"

struct buffer {
  int *buffer;
  int size;
  int current_index;
};

/*@
predicate_ctor buffer_memory
  (struct buffer *buffer, int size)
  (list<int> sigma) = true; // TODO body
@*/





// void buffer_write(struct buffer *buffer, int c);
// requires TODO
// ensures TODO


#endif