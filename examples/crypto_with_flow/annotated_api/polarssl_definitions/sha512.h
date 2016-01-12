#ifndef SHA512_H
#define SHA512_H

#include <string.h>

#include "macro_defines.h"
#include "net.h"

void sha512(const char *input, size_t ilen, char* output, int is384);
  /*@ requires [?f]crypto_chars(?kind, input, ilen, ?cs_pay) &*&
                 ilen >= MINIMAL_STRING_SIZE &*&
               chars(output, ?olen, _) &*&
               is384 == 0 && olen == 64 ||
               is384 == 1 && olen == 48; @*/
  /*@ ensures  [f]crypto_chars(kind, input, ilen, cs_pay) &*&
               cryptogram(output, olen, _, cg_hash(cs_pay)); @*/

void sha512_hmac(const char *key, size_t keylen, const char *input, size_t ilen,
                 char *output, int is384);
  /*@ requires [?f1]cryptogram(key, keylen, ?cs_key, ?cg_key) &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               [?f2]crypto_chars(?kind, input, ilen, ?cs_pay) &*&
                 ilen >= MINIMAL_STRING_SIZE &*&
               chars(output, ?length, _) &*&
               is384 == 0 && length == 64 ||
               is384 == 1 && length == 48; @*/
  /*@ ensures  [f1]cryptogram(key, keylen, cs_key, cg_key) &*&
               [f2]crypto_chars(kind, input, ilen, cs_pay) &*&
               cryptogram(output, length, _, cg_hmac(p, c, cs_pay)); @*/

#endif
