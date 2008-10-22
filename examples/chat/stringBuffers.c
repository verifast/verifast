#include "bool.h"
#include "stringBuffers.h"
#include "stringBuffersExt.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@
predicate string_buffer(struct string_buffer *buffer)
    requires buffer->length |-> ?length &*& buffer->capacity |-> ?capacity &*& buffer->chars |-> ?charsArray &*& malloc_block_string_buffer(buffer) &*& chars(charsArray, ?cs) &*&
        malloc_block(charsArray, capacity) &*& 0 <= length &*& length <= capacity &*& chars_length(cs) == capacity;
@*/

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
    //@ assume_is_int(count);
    int length = buffer->length;
    //@ assume_is_int(length);
    if (2147483647 - buffer->length < count) {
        abort();
    }
    newLength = buffer->length + count;
    if (buffer->capacity < newLength) {
        char *bufferChars = 0;
        char *newChars = malloc(newLength);
        if (newChars == 0) {
            abort();
        }
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
    if (copy == 0 || chars == 0) {
        abort();
    }
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

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures emp;
{
    //@ open string_buffer(buffer);
    free(buffer->chars);
    free(buffer);
}
