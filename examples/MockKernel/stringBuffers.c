#include "stdbool.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@
predicate string_buffer(struct string_buffer *buffer) =
    buffer->length |-> ?length &*& buffer->capacity |-> ?capacity &*& buffer->chars |-> ?charsArray &*& malloc_block_string_buffer(buffer) &*&
    chars(charsArray, ?cs) &*& malloc_block(charsArray, capacity) &*& 0 <= length &*& length <= capacity &*& chars_length(cs) == capacity;
@*/

char *string_buffer_to_string(struct string_buffer *buffer)
{
    char *result;
    string_buffer_append_chars(buffer, "", 1);
    result = buffer->chars;
    free(buffer);
    return result;
}

struct string_buffer *create_string_buffer()
    //@ requires emp;
    //@ ensures string_buffer(result);
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ chars_nil(0);
    //@ malloc_block_null();
    //@ close string_buffer(buffer);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires false; // TODO: Improve this contract.
    //@ ensures true;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& 0 <= result;
{
    //@ open string_buffer(buffer);
    int result = buffer->length;
    //@ close [f]string_buffer(buffer);
    return result;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
{
    //@ open string_buffer(buffer);
    buffer->length = 0;
    //@ close string_buffer(buffer);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& [?f]chars(chars, ?cs) &*& count == chars_length(cs);
    //@ ensures string_buffer(buffer) &*& [f]chars(chars, cs);
{
    int newLength = 0;
    //@ chars_length_nonnegative(cs);
    //@ open string_buffer(buffer);
    //@ malloc_block_limits(buffer->chars);
    int length = buffer->length;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    if (buffer->capacity < newLength) {
        char *bufferChars = 0;
        char *newChars = malloc(newLength);
        if (newChars == 0) abort();
        buffer->capacity = newLength;
        bufferChars = buffer->chars;
        //@ chars_split(buffer->chars, buffer->length);
        //@ chars_split(newChars, buffer->length);
        memcpy(newChars, buffer->chars, buffer->length);
        //@ chars_join(newChars);
        //@ chars_join(bufferChars);
        free(buffer->chars);
        buffer->chars = newChars;
    }
    //@ chars_split(buffer->chars, buffer->length);
    //@ chars_split(buffer->chars + buffer->length, count);
    //@ malloc_block_limits(buffer->chars);
    memcpy(buffer->chars + buffer->length, chars, count);
    //@ chars_join(buffer->chars);
    //@ chars_join(buffer->chars);
    buffer->length = newLength;
    //@ close string_buffer(buffer);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& [?f]string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& [f]string_buffer(buffer0);
{
    //@ open string_buffer(buffer0);
    //@ chars_split(buffer0->chars, buffer0->length);
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ chars_join(buffer0->chars);
    //@ close [f]string_buffer(buffer0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f]chars(string, ?cs) &*& chars_contains(cs, 0) == true;
    //@ ensures string_buffer(buffer) &*& [f]chars(string, cs);
{
    int length = strlen(string);
    //@ chars_contains_chars_index_of(cs, 0);
    //@ chars_split(string, length);
    string_buffer_append_chars(buffer, string, length);
    //@ chars_join(string);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& string_buffer(result);
{
    //@ open string_buffer(buffer);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc(buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    //@ chars_split(buffer->chars, buffer->length);
    memcpy(chars, buffer->chars, buffer->length);
    //@ chars_join(buffer->chars);
    copy->chars = chars;
    //@ close [f]string_buffer(buffer);
    //@ close string_buffer(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires [?f]string_buffer(buffer) &*& [?f0]string_buffer(buffer0);
    //@ ensures [f]string_buffer(buffer) &*& [f0]string_buffer(buffer0);
{
    bool result = false;
    //@ open string_buffer(buffer);
    //@ open string_buffer(buffer0);
    if (buffer->length == buffer0->length) {
        //@ chars_split(buffer->chars, buffer->length);
        //@ chars_split(buffer0->chars, buffer0->length);
        int result0 = memcmp(buffer->chars, buffer0->chars, buffer->length);
        //@ chars_join(buffer->chars);
        //@ chars_join(buffer0->chars);
        result = result0 == 0;
    }
    //@ close [f]string_buffer(buffer);
    //@ close [f0]string_buffer(buffer0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]chars(string, ?cs) &*& chars_contains(cs, 0) == true;
    //@ ensures [f1]string_buffer(buffer) &*& [f2]chars(string, cs);
{
    bool result = false;
    //@ open string_buffer(buffer);
    int length = strlen(string);
    //@ chars_contains_chars_index_of(cs, 0);
    if (length == buffer->length) {
        //@ chars_split(buffer->chars, length);
        //@ chars_split(string, length);
        int result0 = memcmp(buffer->chars, string, length);
        //@ chars_join(buffer->chars);
        //@ chars_join(string);
        result = result0 == 0;
    }
    //@ close [f1]string_buffer(buffer);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures emp;
{
    //@ open string_buffer(buffer);
    free(buffer->chars);
    free(buffer);
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires [?f1]chars(chars, ?charsChars) &*& chars_length(charsChars) == length &*& [?f2]chars(string, ?stringChars) &*& chars_contains(stringChars, 0) == true;
    /*@
    ensures
        [f1]chars(chars, charsChars) &*& [f2]chars(string, stringChars) &*&
        result == -1 ? true : 0 <= result &*& result + chars_index_of(stringChars, 0) <= chars_length(charsChars);
    @*/
{
    int n = strlen(string);
    //@ chars_contains_chars_index_of(stringChars, 0);
    char *p = chars;
    char *end = 0;
    //@ chars_length_nonnegative(charsChars);
    //@ chars_limits(chars);
    end = chars + length;
    while (true)
        //@ invariant [f1]chars(chars, charsChars) &*& [f2]chars(string, stringChars) &*& chars <= p &*& p <= end;
    {
        if (end - p < n) return -1;
        //@ chars_split(chars, p - chars);
        //@ chars_split(p, n);
        //@ chars_split(string, n);
        {
            int cmp = memcmp(p, string, n);
            //@ chars_join(string);
            //@ chars_join(p);
            //@ chars_join(chars);
            if (cmp == 0) return p - chars;
            //@ chars_take_0(stringChars);
            //@ chars_take_0(chars_drop(charsChars, p - chars));
            //@ assert [_]chars(chars, ?charsChars2);
            //@ assert p + 1 - chars <= chars_length(charsChars);
            //@ assert(charsChars2 == charsChars);
            //@ assert p + 1 - chars <= chars_length(charsChars2);
            p++;
            //@ open chars(string, stringChars);
            //@ chars_split(chars, p - chars);
            //@ assert [_]chars(p, ?pChars) &*& [_]character(string, ?c0);        
            p = memchr(p, *string, end - p);
            //@ chars_join(chars);
            //@ close [f2]chars(string, stringChars);
            if (p == 0) return -1;
            //@ chars_contains_chars_index_of(pChars, c0);
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]chars(separator, ?cs) &*& chars_contains(cs, 0) == true &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures [f1]string_buffer(buffer) &*& [f2]chars(separator, cs) &*& string_buffer(before) &*& string_buffer(after);
{
    //@ chars_contains_chars_index_of(cs, 0);
    //@ open string_buffer(buffer);
    int n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ chars_split(chars, buffer->length);
    int index = chars_index_of_string(chars, length, separator);
    //@ chars_join(chars);
    if (index == -1) { /*@ close [f1]string_buffer(buffer); @*/ return false; }
    string_buffer_clear(before);
    //@ chars_split(chars, index);
    string_buffer_append_chars(before, chars, index);
    //@ chars_join(chars);
    string_buffer_clear(after);
    //@ chars_limits(chars);
    //@ chars_split(chars, index + n);
    //@ chars_split(chars + index + n, length - index - n);
    string_buffer_append_chars(after, chars + index + n, length - index - n);
    //@ chars_join(chars + index + n);
    //@ chars_join(chars);
    //@ close [f1]string_buffer(buffer);
    return true;
}
