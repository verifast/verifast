#ifndef SHA512_H
#define SHA512_H

#include <string.h>
//@ #include "crypto/memcmp.gh"

#include "macro_defines.h"
#include "net.h"

void sha512(const char *input, size_t ilen, char* output, int is384);
  /*@ requires [?f]crypto_chars(?kind, input, ilen, ?ccs_pay) &*&
               [_]memcmp_region(_, ccs_pay) &*& chars_(output, ?olen, _) &*&
               is384 == 0 && olen == 64; @*/
  /*@ ensures  [f]crypto_chars(kind, input, ilen, ccs_pay) &*&
               cryptogram(output, olen, _, cg_sha512_hash(ccs_pay)); @*/

void sha512_hmac(const char *key, size_t keylen, const char *input, size_t ilen,
                 char *output, int is384);
  /*@ requires [?f1]cryptogram(key, keylen, ?ccs_key, ?cg_key) &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               [?f2]crypto_chars(?kind, input, ilen, ?ccs_pay) &*&
                 ilen >= MINIMAL_STRING_SIZE &*&
               [_]memcmp_region(_, ccs_pay) &*& chars_(output, ?length, _) &*&
               is384 == 0 && length == 64; @*/
  /*@ ensures  [f1]cryptogram(key, keylen, ccs_key, cg_key) &*&
               [f2]crypto_chars(kind, input, ilen, ccs_pay) &*&
               cryptogram(output, length, _, cg_sha512_hmac(p, c, ccs_pay)); @*/

#endif
