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
  chars_(context->content, AES_CONTEXT_SIZE, _) &*&
  struct_aes_context_padding(context)
;

predicate aes_context_initialized(aes_context *context,
                                  int principal, int count);

@*/

int aes_setkey_enc(aes_context *ctx, const char *key, unsigned int keysize);
  /*@ requires [?f]cryptogram(key, ?size_key, ?ccs_key, ?cg_key) &*&
                 keysize == size_key * 8 &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               aes_context(ctx) &*&
               (keysize == 128 || keysize == 192 || keysize == 256); @*/
  /*@ ensures  [f]cryptogram(key, size_key, ccs_key, cg_key) &*&
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
               crypto_chars(?iv_kind, iv, 16, ?iv_ccs) &*&
               *iv_off |-> 0 &*&
               chars_(output, length, _) &*& mode == AES_ENCRYPT ?
               (
                 random_permission(?p2, ?c2) &*&
                 iv_ccs == ccs_for_cg(cg_nonce(p2, c2)) &*&
                 [?f]crypto_chars(?kind, input, length, ?in_ccs) &*&
                   length >= MINIMAL_STRING_SIZE &*&
                 ensures
                 (
                   aes_context_initialized(ctx, p1, c1) &*&
                   // this increment enforces a fresh IV on each invocation
                   random_permission(p2, c2 + 1) &*&
                   [f]crypto_chars(kind, input, length, in_ccs) &*&
                   // content of updated iv is correlated with input
                   crypto_chars(join_kinds(iv_kind, kind), iv, 16, _) &*&
                   *iv_off |-> ?_ &*&
                   result != 0 ?
                     // encryption failed
                     chars(output, length, _)
                   :
                     // encryption was successful
                     cryptogram(output, length, _, ?cg) &*&
                     cg == cg_aes_encrypted(p1, c1, in_ccs, iv_ccs)
                 )
               )
               :
               (
                 decryption_pre(true, ?garbage_in, ?p2, ?s, ?in_ccs) &*&
                 [?f]cryptogram(input, length, in_ccs, ?cg) &*&
                   cg == cg_aes_encrypted(?p3, ?c3, ?out_ccs3, ?iv_ccs3) &*&
                 ensures
                 (
                   aes_context_initialized(ctx, p1, c1) &*&
                   [f]cryptogram(input, length, in_ccs, cg) &*&
                   *iv_off |-> ?_ &*&
                   crypto_chars(?kind, output, length, ?out_ccs) &*&
                   // content of updated iv is correlated with output
                   crypto_chars(join_kinds(iv_kind, kind), iv, 16, _) &*&
                   decryption_post(true, ?garbage_out, 
                                   p2, s, p1, c1, out_ccs) &*&
                   garbage_out == (garbage_in || p1 != p3 || 
                                   c1 != c3 || iv_ccs != iv_ccs3) &*&
                   result != 0 || garbage_out ?
                     kind == normal
                   :
                     kind == secret && out_ccs == out_ccs3
                 )
               ); @*/
  //@ ensures  true;

#endif
