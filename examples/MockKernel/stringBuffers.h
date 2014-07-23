#ifndef STRINGBUFFERS_H
#define STRINGBUFFERS_H

#include "stdbool.h"

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
bool string_buffer_equals_string(struct string_buffer *buffer, char *string);
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]chars(string, ?n, ?cs) &*& mem('\0', cs) == true;
    //@ ensures [f1]string_buffer(buffer) &*& [f2]chars(string, n, cs);
void string_buffer_clear(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    //@ requires string_buffer(buffer) &*& [?f]chars(chars, ?n, ?cs) &*& count == length(cs);
    //@ ensures string_buffer(buffer) &*& [f]chars(chars, n, cs);
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer) &*& [?f]string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& [f]string_buffer(buffer0);
void string_buffer_append_string(struct string_buffer *buffer, char *string);
    //@ requires string_buffer(buffer) &*& [?f]chars(string, ?n, ?cs) &*& mem('\0', cs) == true;
    //@ ensures string_buffer(buffer) &*& [f]chars(string, n, cs);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& string_buffer(result);
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after);
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]chars(separator, ?n, ?cs) &*& mem('\0', cs) == true &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures [f1]string_buffer(buffer) &*& [f2]chars(separator, n, cs) &*& string_buffer(before) &*& string_buffer(after);
void string_buffer_dispose(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures emp;
char *string_buffer_to_string(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures chars(result, ?n, ?cs) &*& mem('\0', cs) == true;

#endif
