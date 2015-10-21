#ifndef STRINGBUFFERS_H
#define STRINGBUFFERS_H

#include <stdbool.h>

struct string_buffer;

/*@
predicate string_buffer(struct string_buffer *buffer; list<char> cs);
predicate string_buffer_minus_chars(struct string_buffer *buffer; char *pcs, int length);

lemma void string_buffer_merge_chars(struct string_buffer *buffer);
    requires [?f]string_buffer_minus_chars(buffer, ?pcs, ?n) &*& [f]chars(pcs, n, ?cs);
    ensures [f]string_buffer(buffer, cs);

lemma_auto void string_buffer_not_null();
    requires string_buffer(?buffer, ?cs);
    ensures string_buffer(buffer, cs) &*& buffer != 0;
@*/

struct string_buffer *create_string_buffer();
    //@ requires emp;
    //@ ensures string_buffer(result, nil) &*& result != 0;
int string_buffer_get_length(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& result == length(cs);
char *string_buffer_get_chars(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer_minus_chars(buffer, result, length(cs)) &*& [f]chars(result, length(cs), cs);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires [?f]string_buffer(buffer, ?cs) &*& [?f0]string_buffer(buffer0, ?cs0);
    //@ ensures [f]string_buffer(buffer, cs) &*& [f0]string_buffer(buffer0, cs0) &*& result == (cs == cs0);
bool string_buffer_equals_string(struct string_buffer *buffer, char *string);
    //@ requires [?f1]string_buffer(buffer, ?cs1) &*& [?f2]string(string, ?cs2);
    //@ ensures [f1]string_buffer(buffer, cs1) &*& [f2]string(string, cs2) &*& result == (cs1 == cs2);
void string_buffer_clear(struct string_buffer *buffer);
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, nil);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    //@ requires string_buffer(buffer, ?bcs) &*& [?f]chars(chars, count, ?cs);
    //@ ensures string_buffer(buffer, append(bcs, cs)) &*& [f]chars(chars, count, cs);
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, append(cs, cs0)) &*& [f]string_buffer(buffer0, cs0);
void string_buffer_append_string(struct string_buffer *buffer, char *string);
    //@ requires string_buffer(buffer, ?bcs) &*& [?f]string(string, ?cs);
    //@ ensures string_buffer(buffer, append(bcs, cs)) &*& [f]string(string, cs);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& string_buffer(result, cs);
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after);
    //@ requires [?f1]string_buffer(buffer, ?bcs) &*& [?f2]string(separator, ?cs) &*& string_buffer(before, _) &*& string_buffer(after, _);
    //@ ensures [f1]string_buffer(buffer, bcs) &*& [f2]string(separator, cs) &*& string_buffer(before, _) &*& string_buffer(after, _);
void string_buffer_drop_front(struct string_buffer *buffer, int length);
    //@ requires string_buffer(buffer, ?bcs) &*& length >= 0;
    //@ ensures string_buffer(buffer, _);
void string_buffer_dispose(struct string_buffer *buffer);
    //@ requires buffer == 0 ? emp : string_buffer(buffer, _);
    //@ ensures emp;

#endif
