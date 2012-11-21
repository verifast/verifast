#include "bool.h"
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@

predicate string_buffer(struct string_buffer *buffer; list<char> cs) =
    buffer->length |-> ?length &*&
    buffer->capacity |-> ?capacity &*&
    buffer->chars |-> ?charsArray &*&
    malloc_block_string_buffer(buffer) &*&
    charsArray[0..length] |-> cs &*&
    charsArray[length..capacity] |-> _ &*&
    malloc_block(charsArray, capacity);

predicate string_buffer_minus_chars(struct string_buffer *buffer; char *charsArray, int length) =
    buffer->length |-> length &*&
    buffer->capacity |-> ?capacity &*&
    buffer->chars |-> charsArray &*&
    malloc_block_string_buffer(buffer) &*&
    charsArray[length..capacity] |-> _ &*&
    malloc_block(charsArray, capacity) &*&
    0 <= length;

lemma void string_buffer_merge_chars(struct string_buffer *buffer)
    requires [?f]string_buffer_minus_chars(buffer, ?pcs, ?n) &*& [f]chars(pcs, ?cs) &*& length(cs) == n;
    ensures [f]string_buffer(buffer, cs);
{
    chars_to_char_array(pcs);
    close [f]string_buffer(buffer, cs);
}

@*/

struct string_buffer *create_string_buffer()
    //@ requires emp;
    //@ ensures string_buffer(result, nil);
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ malloc_block_null();
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer_minus_chars(buffer, result, length(cs)) &*& [f]chars(result, cs);
{
    return buffer->chars;
    //@ char_array_to_chars(buffer->chars);
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& result == length(cs);
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, nil);
{
    buffer->length = 0;
    //@ array_merge(buffer->chars);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    /*@
    requires
        buffer->length |-> ?length &*&
        buffer->capacity |-> ?capacity0 &*&
        buffer->chars |-> ?charsArray0 &*&
        array<char>(charsArray0, length, 1, character, ?cs) &*&
        array<char>(charsArray0 + length, capacity0 - length, 1, character, _) &*&
        malloc_block(charsArray0, capacity0);
    @*/
    /*@
    ensures
        buffer->length |-> length &*&
        buffer->capacity |-> ?capacity1 &*&
        buffer->chars |-> ?charsArray1 &*&
        array<char>(charsArray1, length, 1, character, cs) &*&
        array<char>(charsArray1 + length, capacity1 - length, 1, character, _) &*&
        malloc_block(charsArray1, capacity1) &*&
        newCapacity <= capacity1;
    @*/
{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc(newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        //@ char_array_to_chars(buffer->chars);
        //@ chars_split(newChars, buffer->length);
        memcpy(newChars, buffer->chars, buffer->length);
        //@ char_array_to_chars(buffer->chars + length);
        //@ chars_join(buffer->chars);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ chars_to_char_array(newChars);
        //@ chars_to_char_array(newChars + buffer->length);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?bcs) &*& [?f]chars(chars, ?cs) &*& count == length(cs);
    //@ ensures string_buffer(buffer, append(bcs, cs)) &*& [f]chars(chars, cs);
{
    int newLength = 0;
    //@ malloc_block_limits(buffer->chars);
    int length = buffer->length;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    //@ char_array_to_chars(buffer->chars + buffer->length);
    //@ chars_split(buffer->chars + buffer->length, count);
    //@ malloc_block_limits(buffer->chars);
    memcpy(buffer->chars + buffer->length, chars, count);
    //@ chars_to_char_array(buffer->chars + buffer->length);
    //@ chars_to_char_array(buffer->chars + buffer->length + count);
    //@ array_merge(buffer->chars);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, append(cs, cs0)) &*& [f]string_buffer(buffer0, cs0);
{
    //@ char_array_to_chars(buffer0->chars);
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ chars_to_char_array(buffer0->chars);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?bcs) &*& [?f]chars(string, ?cs) &*& mem('\0', cs) == true;
    //@ ensures string_buffer(buffer, append(bcs, take(index_of('\0', cs), cs))) &*& [f]chars(string, cs);
{
    int length = strlen(string);
    //@ chars_split(string, length);
    string_buffer_append_chars(buffer, string, length);
    //@ chars_join(string);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& string_buffer(result, cs);
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc(buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    //@ char_array_to_chars(buffer->chars);
    memcpy(chars, buffer->chars, buffer->length);
    //@ chars_to_char_array(buffer->chars);
    //@ chars_to_char_array(chars);
    copy->chars = chars;
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires [?f]string_buffer(buffer, ?cs) &*& [?f0]string_buffer(buffer0, ?cs0);
    //@ ensures [f]string_buffer(buffer, cs) &*& [f0]string_buffer(buffer0, cs0) &*& result == (cs == cs0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        //@ char_array_to_chars(buffer->chars);
        //@ char_array_to_chars(buffer0->chars);
        int result0 = memcmp(buffer->chars, buffer0->chars, buffer->length);
        //@ chars_to_char_array(buffer->chars);
        //@ chars_to_char_array(buffer0->chars);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires [?f1]string_buffer(buffer, ?cs1) &*& [?f2]chars(string, ?cs2) &*& mem('\0', cs2) == true;
    //@ ensures [f1]string_buffer(buffer, cs1) &*& [f2]chars(string, cs2) &*& result == (cs1 == take(index_of('\0', cs2), cs2));
{
    bool result = false;
    int length = strlen(string);
    if (length == buffer->length) {
        //@ char_array_to_chars(buffer->chars);
        //@ chars_split(string, length);
        int result0 = memcmp(buffer->chars, string, length);
        //@ chars_join(string);
        //@ chars_to_char_array(buffer->chars);
        result = result0 == 0;
    }
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, _);
    //@ ensures emp;
{
    //@ array_merge(buffer->chars);
    //@ char_array_to_chars(buffer->chars);
    free((void *)buffer->chars);
    free(buffer);
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires [?f1]chars(chars, ?charsChars) &*& length(charsChars) == length &*& [?f2]chars(string, ?stringChars) &*& mem('\0', stringChars) == true;
    /*@
    ensures
        [f1]chars(chars, charsChars) &*& [f2]chars(string, stringChars) &*&
        result == -1 ? true : 0 <= result &*& result + index_of('\0', stringChars) <= length(charsChars);
    @*/
{
    int n = strlen(string);
    char *p = chars;
    char *end = 0;
    //@ length_nonnegative(charsChars);
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
            //@ take_0(stringChars);
            //@ take_0(drop(p - chars, charsChars));
            //@ assert [_]chars(chars, ?charsChars2);
            //@ assert p + 1 - chars <= length(charsChars);
            //@ assert(charsChars2 == charsChars);
            //@ assert p + 1 - chars <= length(charsChars2);
            p++;
            //@ open chars(string, stringChars);
            //@ chars_split(chars, p - chars);
            //@ assert [_]chars(p, ?pChars) &*& [_]character(string, ?c0);        
            p = memchr(p, *string, end - p);
            //@ chars_join(chars);
            //@ close [f2]chars(string, stringChars);
            if (p == 0) return -1;
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires [?f1]string_buffer(buffer, ?bcs) &*& [?f2]chars(separator, ?cs) &*& mem('\0', cs) == true &*& string_buffer(before, _) &*& string_buffer(after, _);
    //@ ensures [f1]string_buffer(buffer, bcs) &*& [f2]chars(separator, cs) &*& string_buffer(before, _) &*& string_buffer(after, _);
{
    int n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ char_array_to_chars(buffer->chars);
    int index = chars_index_of_string(chars, length, separator);
    //@ chars_to_char_array(buffer->chars);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    //@ char_array_to_chars(buffer->chars);
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
    //@ chars_to_char_array(chars);
    return true;
}