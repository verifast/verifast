#ifndef GCM_H
#define GCM_H

#include "macro_defines.h"
#include "net.h"

#define GCM_ENCRYPT   1
#define GCM_DECRYPT   0

struct gcm_context
{
  char content[GCM_CONTEXT_SIZE];
};
typedef struct gcm_context gcm_context;

/*@

predicate gcm_context(gcm_context *context) =
  chars((void*) context, GCM_CONTEXT_SIZE, _) &*&
  struct_gcm_context_padding(context)
;
predicate gcm_context_initialized(gcm_context *context,
                                  int principal, int count);

@*/

int gcm_init(gcm_context *ctx, int cipher,
             const char *key, unsigned int keysize);
  /*@ requires [?f]cryptogram(key, ?size_key, ?cs_key, ?cg_key) &*&
                 keysize == size_key * 8 &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               gcm_context(ctx) &*&
               (keysize == 128 || keysize == 192 || keysize == 256) &*&
               // only AES supported for now
               cipher == POLARSSL_CIPHER_ID_AES; @*/
  /*@ ensures  [f]cryptogram(key, size_key, cs_key, cg_key) &*&
               result == 0 ?
                 gcm_context_initialized(ctx, p, c)
               :
                 gcm_context(ctx); @*/

void gcm_free(gcm_context *ctx);
  //@ requires gcm_context_initialized(ctx, _, _);
  //@ ensures  gcm_context(ctx);

int gcm_crypt_and_tag(gcm_context *ctx, int mode, size_t length,
                      const char *iv, size_t iv_len,
                      const char *add, size_t add_len,
                      const char *input, char *output,
                      size_t tag_len, char *tag);
  /*@ requires gcm_context_initialized(ctx, ?p1, ?c1) &*&
               random_permission(?p2, ?c2) &*&
               // this function is only spec'ed for encryption
               // use the function gcm_auth_decrypt to decrypt
               (mode == GCM_ENCRYPT) &*&
               // iv_len must be 16 since only AES is supported (see gcm_init)
               cryptogram(iv, iv_len, ?iv_cs, ?iv_cg) &*&
                 iv_len == 16 &*& iv_cg == cg_nonce(p2, c2) &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f]crypto_chars(?kind, input, length, ?in_cs) &*&
                 length >= MINIMAL_STRING_SIZE &*&
               // only tags of 16 bytes for simplicity
               chars(tag, tag_len, _) &*& tag_len == 16 &*&
               chars(output, length, _); @*/
  /*@ ensures  gcm_context_initialized(ctx, p1, c1) &*&
               random_permission(p2, c2) &*&
               // content of updated iv is correlated with input
               crypto_chars(kind, iv, iv_len, _) &*&
               [f]crypto_chars(kind, input, length, in_cs) &*&
               chars(tag, tag_len, ?tag_cs) &*&
               result != 0 ?
                 // encryption failed
                 chars(output, length, _)
               :
                 // encryption was successful
                 cryptogram(output, length, _, ?cg) &*&
                 cg == cg_auth_encrypted(p1, c1, in_cs, tag_cs, iv_cs); @*/

int gcm_auth_decrypt(gcm_context *ctx, size_t length,
                     const char *iv, size_t iv_len,
                     const char *add, size_t add_len,
                     const char *tag, size_t tag_len,
                     const char *input, char *output);
  /*@ requires gcm_context_initialized(ctx, ?p1, ?c1) &*&
               // iv_len must be 16 since only AES is supported (see gcm_init)
               cryptogram(iv, iv_len, ?iv_cs, ?iv_cg) &*& iv_len == 16 &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f]cryptogram(input, length, ?in_cs, ?in_cg) &*&
                  in_cg == cg_auth_encrypted(?p2, ?c2, ?out_cs2,
                                             ?tag_cs2, ?iv_cs2) &*&
                  length >= MINIMAL_STRING_SIZE &*&
               // only tags of 16 bytes for simplicity
               chars(tag, tag_len, ?tag_cs) &*& tag_len == 16 &*&
               chars(output, length, _); @*/
  /*@ ensures  gcm_context_initialized(ctx, p1, c1) &*&
               [f]cryptogram(input, length, in_cs, in_cg) &*&
               chars(tag, tag_len, _) &*&
               result != 0 ?
                 // content of updated iv is correlated with output
                 chars(iv, iv_len, _) &*&
                 chars(output, length, _)
               :
                 // content of updated iv is correlated with output
                 crypto_chars(secret, iv, iv_len, _) &*&
                 crypto_chars(secret, output, length, ?out_cs) &*&
                 col || (p1 == p2 && c1 == c2 && tag_cs == tag_cs2 &&
                         iv_cs == iv_cs2 && out_cs == out_cs2); @*/

#endif
