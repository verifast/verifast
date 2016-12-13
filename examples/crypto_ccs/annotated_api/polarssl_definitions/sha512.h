#ifndef SHA512_H
#define SHA512_H

#include <string.h>

#include "macro_defines.h"
#include "net.h"

/*@

fixpoint bool cg_with_entropy(cryptogram cg)
{
  switch(cg)
  {
    case cg_hash(cs1):
      return false;
    case cg_hmac(p1, c1, cs1):
      return false;
    default:
      return true;
  }
}

predicate hash_payload(bool public, list<crypto_char> ccs) =
  public ?
    [_]public_ccs(ccs)
  :
    [_]exists(?cg) &*& sublist(ccs_for_cg(cg), ccs) && cg_with_entropy(cg)
;

#define HASH_PUB_PAYLOAD(PAY) \
  { \
    public_cs(PAY); \
    close hash_payload(true, cs_to_ccs(PAY)); \
    leak hash_payload(true, cs_to_ccs(PAY)); \
  }
@*/

void sha512(const char *input, size_t ilen, char* output, int is384);
  /*@ requires [?f]crypto_chars(?kind, input, ilen, ?ccs_pay) &*&
               [_]hash_payload(_, ccs_pay) &*&
               chars(output, ?olen, _) &*&
               is384 == 0 && olen == 64 || is384 == 1 && olen == 48; @*/
  /*@ ensures  [f]crypto_chars(kind, input, ilen, ccs_pay) &*&
               cryptogram(output, olen, _, cg_hash(ccs_pay)); @*/

void sha512_hmac(const char *key, size_t keylen, const char *input, size_t ilen,
                 char *output, int is384);
  /*@ requires [?f1]cryptogram(key, keylen, ?ccs_key, ?cg_key) &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               [?f2]crypto_chars(?kind, input, ilen, ?ccs_pay) &*&
                 [_]hash_payload(_, ccs_pay) &*&
                 ilen >= MINIMAL_STRING_SIZE &*&
               chars(output, ?length, _) &*&
               is384 == 0 && length == 64 || is384 == 1 && length == 48; @*/
  /*@ ensures  [f1]cryptogram(key, keylen, ccs_key, cg_key) &*&
               [f2]crypto_chars(kind, input, ilen, ccs_pay) &*&
               cryptogram(output, length, _, cg_hmac(p, c, ccs_pay)); @*/

#endif
