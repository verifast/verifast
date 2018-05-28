#ifndef STRING_H
#define STRING_H

#include <stddef.h>

char *strcpy(char *d, char *s);
    //@ requires [?f]string(s, ?cs) &*& chars(d, length(cs) + 1, _);
    //@ ensures [f]string(s, cs) &*& chars(d, length(cs) + 1, append(cs, {0})) &*& result == d;

void memcpy(void *arr, void *arr0, size_t count);
    //@ requires chars(arr, count, ?cs) &*& [?f]chars(arr0, count, ?cs0);
    //@ ensures chars(arr, count, cs0) &*& [f]chars(arr0, count, cs0);

void memmove(void *dest, void *src, size_t count);
    /*@
    requires
        chars(src, count, ?cs) &*&
        dest <= src ?
            chars(dest, src - dest, _)
        :
            chars(src + count, dest - src, _);
    @*/
    /*@
    ensures
        chars(dest, count, cs) &*&
        dest <= src ?
            chars(dest + count, src - dest, _)
        :
            chars(src, dest - src, _);
    @*/

int strlen(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == length(cs);

int memcmp(char *arr, char *arr0, size_t count);
    //@ requires [?f]chars(arr, ?n, ?cs) &*& [?f0]chars(arr0, ?n0, ?cs0) &*& count <= n &*& count <= n0;
    //@ ensures [f]chars(arr, n, cs) &*& [f0]chars(arr0, n0, cs0) &*& (result == 0) == (take(count, cs) == take(count, cs0));

int strcmp(char *s1, char *s2);
    //@ requires [?f1]string(s1, ?cs1) &*& [?f2]string(s2, ?cs2);
    //@ ensures [f1]string(s1, cs1) &*& [f2]string(s2, cs2) &*& (result == 0) == (cs1 == cs2);

char *memchr(char *arr, char c, size_t count);
    //@ requires [?f]chars(arr, count, ?cs);
    //@ ensures [f]chars(arr, count, cs) &*& result == 0 ? mem(c, cs) == false : mem(c, cs) == true &*& result == arr + index_of(c, cs);

char* strchr(char *str, char c);
    //@ requires [?f]string(str, ?cs);
    /*@ ensures
            [f]string(str, cs) &*&
            c == 0 ?
                result == str + length(cs)
            :
                result == 0 ?
                    mem(c, cs) == false
                :
                    mem(c, cs) == true &*& result == str + index_of(c, cs);
    @*/

void* memset(void *arr, char value, size_t size);
    //@ requires chars(arr, size, ?cs);
    //@ ensures chars(arr, size, ?cs1) &*& all_eq(cs1, value) == true &*& result == arr;

char *strdup(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == 0 ? true : string(result, cs) &*& malloc_block_chars(result, length(cs) + 1);

#endif
