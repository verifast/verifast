#ifndef STRINGBUFFERSEXT_H
#define STRINGBUFFERSEXT_H

#include "stringBuffers.h"

char *string_buffer_get_chars(struct string_buffer *buffer);
    //@ requires false; // TODO: Improve this contract.
    //@ ensures true;

int string_buffer_get_length(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& 0 <= result;

void string_buffer_clear(struct string_buffer *buffer);
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    //@ requires string_buffer(buffer) &*& [?f]chars(chars, ?cs) &*& count == chars_length(cs);
    //@ ensures string_buffer(buffer) &*& [f]chars(chars, cs);

#endif