#ifndef STRING_H
#define STRING_H

#include <stddef.h>
//@ #include <crypto.gh>

char *strcpy(char *d, char *s);
    //@ requires [?f]string(s, ?cs) &*& chars(d, length(cs) + 1, _);
    //@ ensures [f]string(s, cs) &*& chars(d, length(cs) + 1, append(cs, {0})) &*& result == d;

void memcpy(void *arr, void *arr0, size_t count);
    /*@ requires chars(arr, count, ?cs) &*&
                 [?f]crypto_chars(?kind, arr0, count, ?cs0); @*/
    /*@ ensures  crypto_chars(kind, arr, count, cs0) &*&
                 [f]crypto_chars(kind, arr0, count, cs0); @*/

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

/*@
predicate memcmp_secret(char* buffer, int count, list<char> cs, cryptogram cg) =
  count == length(cs) && cs == chars_for_cg(cg) && cg_is_generated(cg) 
;
@*/

int memcmp(char *arr, char *arr0, size_t count);
    /*@ requires network_permission(?principal) &*& 
                 [?f1]crypto_chars(?kind1, arr, ?n1, ?cs1) &*&
                   (kind1 == normal ? true : 
                      memcmp_secret(arr, count, cs1, _)) &*&
                 [?f2]crypto_chars(?kind2, arr0, ?n2, ?cs2) &*& 
                   (kind2 == normal ? true : 
                      memcmp_secret(arr0, count, cs2, _)) &*&
                 count <= n1 &*& count <= n2; @*/
    /*@ ensures  [f1]crypto_chars(kind1, arr, n1, cs1) &*&
                 [f2]crypto_chars(kind2, arr0, n2, cs2) &*&
                 true == ((result == 0) == (take(count, cs1) == take(count, cs2))) &*&
                 (
                   //if guessing a secret value failed, network permissions are revoked
                   // *otherwise one could keep guessing untill success
                   result != 0 && (kind1 == secret || kind2 == secret) ?
                       true : network_permission(principal)
                 ); @*/

int strcmp(char *s1, char *s2);
    //@ requires [?f1]string(s1, ?cs1) &*& [?f2]string(s2, ?cs2);
    //@ ensures [f1]string(s1, cs1) &*& [f2]string(s2, cs2) &*& true == ((result == 0) == (cs1 == cs2));

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
