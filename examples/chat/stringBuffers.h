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
int string_buffer_get_length(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& 0 <= result;
char *string_buffer_get_chars(struct string_buffer *buffer);
    //@ requires false; // TODO: Improve this contract.
    //@ ensures true;
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires [?f]string_buffer(buffer) &*& [?f0]string_buffer(buffer0);
    //@ ensures [f]string_buffer(buffer) &*& [f0]string_buffer(buffer0);
void string_buffer_clear(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    //@ requires string_buffer(buffer) &*& [?f]chars(chars, ?cs) &*& count == chars_length(cs);
    //@ ensures string_buffer(buffer) &*& [f]chars(chars, cs);
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer) &*& [?f]string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& [f]string_buffer(buffer0);
void string_buffer_append_string(struct string_buffer *buffer, char *string);
    //@ requires string_buffer(buffer) &*& [?f]chars(string, ?cs) &*& chars_contains(cs, 0) == true;
    //@ ensures string_buffer(buffer) &*& [f]chars(string, cs);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& string_buffer(result);
void string_buffer_dispose(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures emp;

#endif