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
  /*@ requires gcm_context_initialized(ctx, ?p, ?c) &*&
               // this function is only spec'ed for encryption, use the function 
               // gcm_auth_decrypt to decrypt
               (mode == GCM_ENCRYPT) &*&
               // iv_len must be 16 since only AES is supported
               chars(iv, iv_len, ?cs_iv) &*& iv_len == 16 &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f]optional_crypto_chars(?cc, input, length, ?cs_in) &*&
                 length >= MIN_ENC_SIZE &*&
               chars(tag, 16, ?tag_cs_in) &*& 
               chars(output, length, _); @*/
  /*@ ensures  gcm_context_initialized(ctx, p, c) &*&
               chars(iv, 16, _) &*&
               [f]optional_crypto_chars(cc, input, length, cs_in) &*&
               chars(tag, tag_len, ?tag_cs_out) &*&
               result == 0 ?
                 cryptogram(output, length, _, ?cg_out) &*&
                 cg_out == cg_auth_encrypted(p, c, tag_cs_out, cs_in, cs_iv)
               :
                 chars(output, length, _); @*/

int gcm_auth_decrypt(gcm_context *ctx, size_t length,
                     const char *iv, size_t iv_len,
                     const char *add, size_t add_len,
                     const char *tag, size_t tag_len,
                     const char *input, char *output);
  /*@ requires gcm_context_initialized(ctx, ?p, ?c) &*&
               // iv_len must be 16 since only AES is supported
               chars(iv, iv_len, ?cs_iv) &*& iv_len == 16 &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f]optional_crypto_chars(?cc, input, length, ?cs_in) &*&
                 length >= MIN_ENC_SIZE &*&
               chars(tag, 16, ?tag_cs_in) &*& 
               chars(output, length, _); @*/
  /*@ ensures gcm_context_initialized(ctx, p, c) &*&
              chars(iv, 16, _) &*&
              [f]optional_crypto_chars(cc, input, length, cs_in) &*&
              chars(tag, tag_len, _) &*&
              result == 0 ?
                crypto_chars(output, length, ?cs_out) &*&
                cs_in == chars_for_cg(cg_auth_encrypted(p, c, tag_cs_in, 
                                                        cs_out, cs_iv))
              :
                chars(output, length, _); @*/

#endif