#ifndef AES_H
#define AES_H

#include "macro_defines.h"
#include "net.h"

#define AES_ENCRYPT 1
#define AES_DECRYPT 0

struct aes_context
{
  char content[AES_CONTEXT_SIZE];
};
typedef struct aes_context aes_context;

/*@

predicate aes_context(aes_context *context) =
  chars((void*) context, AES_CONTEXT_SIZE, _) &*&
  struct_aes_context_padding(context)
;

predicate aes_context_initialized(aes_context *context,
                                  int principal, int count);

@*/

int aes_setkey_enc(aes_context *ctx, const char *key, unsigned int keysize);
  /*@ requires [?f]cryptogram(key, ?size_key, ?cs_key, ?cg_key) &*&
                 keysize == size_key * 8 &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               aes_context(ctx) &*&
               (keysize == 128 || keysize == 192 || keysize == 256); @*/
  /*@ ensures  [f]cryptogram(key, size_key, cs_key, cg_key) &*&
               result == 0 ?
                 aes_context_initialized(ctx, p, c)
               :
                 aes_context(ctx); @*/

void aes_free(aes_context *ctx);
  //@ requires aes_context_initialized(ctx, _, _);
  //@ ensures  aes_context(ctx);

int aes_crypt_cfb128(aes_context *ctx, int mode, size_t length, size_t *iv_off,
                     char *iv, const char *input, char *output);
  /*@ requires mode == AES_ENCRYPT || mode == AES_DECRYPT &*&
               aes_context_initialized(ctx, ?p1, ?c1) &*&
               // AES only supports an iv with a length of 16 bytes
               // only zero offset allowed, not spec'ed for CBF mode
               cryptogram(iv, 16, ?iv_cs, ?iv_cg) &*&  u_integer(iv_off, 0) &*&
               chars(output, length, _) &*& mode == AES_ENCRYPT ?
               (
                 principal(?p2, ?c2) &*& iv_cg == cg_nonce(p2, c2) &*&
                 [?f]crypto_chars(?kind, input, length, ?in_cs) &*&
                 ensures
                 (
                   principal(p2, c2) &*&
                   aes_context_initialized(ctx, p1, c1) &*&
                   [f]crypto_chars(kind, input, length, in_cs) &*&
                   // content of updated iv is correlated with input
                   crypto_chars(kind, iv, 16, _) &*&
                   u_integer(iv_off, _) &*&
                   kind == garbage ?
                     // got garbage as input
                     crypto_chars(garbage, output, length, _)
                   : result != 0 ?
                     // encryption failed
                     chars(output, length, _)
                   : 
                     // encryption was successful
                     cryptogram(output, length, _, ?cg) &*&
                     cg == cg_encrypted(p1, c1, in_cs, iv_cs)
                 )
               )
               :
               (
                 [?f]cryptogram(input, length, ?in_cs, ?cg) &*&
                   cg == cg_encrypted(?p2, ?c2, ?out_cs2, ?iv_cs2) &*&
                 ensures
                 (
                   aes_context_initialized(ctx, p1, c1) &*&
                   [f]cryptogram(input, length, in_cs, cg) &*&
                   u_integer(iv_off, _) &*&
                   result != 0 ?
                     // content of updated iv is correlated with output
                     chars(iv, 16, _) &*&
                     chars(output, length, _)
                   : col || p1 != p2 || c1 != c2 ?
                     // content of updated iv is correlated with output
                     crypto_chars(garbage, iv, 16, _) &*&
                     crypto_chars(garbage, output, length, ?out_cs) &*&
                     true == decrypted_garbage(out_cs)
                   :
                     // content of updated iv is correlated with output
                     crypto_chars(secret, iv, 16, _) &*&
                     crypto_chars(secret, output, length, ?out_cs) &*&
                     out_cs == out_cs2 && iv_cs == iv_cs2
                 )
               ); @*/
  //@ ensures  true;

#endif
