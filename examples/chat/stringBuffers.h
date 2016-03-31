#ifndef STRINGBUFFERS_H
#define STRINGBUFFERS_H

#include "bool.h"

struct string_buffer;

/*@
predicate string_buffer(struct string_buffer *buffer);
@*/

struct string_buffer *create_string_buffer();
    //@ requires emp;
    //@ ensures string_buffer(result);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& string_buffer(result);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
void string_buffer_dispose(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures emp;

#endif