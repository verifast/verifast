#ifndef CRYPTO_STRING_H
#define CRYPTO_STRING_H

#include <stddef.h>

//@ #include "crypto/memcmp.gh"

void crypto_memcpy(void *array, void *array0, size_t count);
    /*@ requires chars_(array, count, _) &*&
                 [?f]crypto_chars(?kind, array0, count, ?ccs0); @*/
    /*@ ensures  crypto_chars(kind, array, count, ccs0) &*&
                 [f]crypto_chars(kind, array0, count, ccs0); @*/

int crypto_memcmp(char *array, char *array0, size_t count);
    /*@ requires [?f1]crypto_chars(?kind1, array, ?n1, ?ccs1) &*&
                 [_]memcmp_region(?l1, take(count, ccs1)) &*& 
                 [?f2]crypto_chars(?kind2, array0, ?n2, ?ccs2) &*& 
                 [_]memcmp_region(?l2, take(count, ccs2)) &*& 
                 memcmp_match(l1, l2) && count <= n1 && count <= n2; @*/
    /*@ ensures  [f1]crypto_chars(kind1, array, n1, ccs1) &*&
                 [f2]crypto_chars(kind2, array0, n2, ccs2) &*&
                 true == ((result == 0) == (take(count, ccs1) == take(count, ccs2))); @*/

#endif
