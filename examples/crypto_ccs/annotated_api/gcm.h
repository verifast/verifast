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
  chars_(context->content, GCM_CONTEXT_SIZE, _) &*&
  struct_gcm_context_padding(context)
;
predicate gcm_context_initialized(gcm_context *context,
                                  int principal, int count);

@*/

int gcm_init(gcm_context *ctx, int cipher,
             const char *key, unsigned int keysize);
  /*@ requires [?f]cryptogram(key, ?size_key, ?ccs_key, ?cg_key) &*&
                 keysize == size_key * 8 &*&
                 cg_key == cg_symmetric_key(?p, ?c) &*&
               gcm_context(ctx) &*&
               (keysize == 128 || keysize == 192 || keysize == 256) &*&
               // only AES supported for now
               cipher == MBEDTLS_CIPHER_ID_AES; @*/
  /*@ ensures  [f]cryptogram(key, size_key, ccs_key, cg_key) &*&
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
               mode == GCM_ENCRYPT &*&
               // iv_len must be 16 since only AES is supported (see gcm_init)
               crypto_chars(?iv_kind, iv, iv_len, ?iv_ccs) &*&
                 iv_len == 16 &*& iv_ccs == ccs_for_cg(cg_nonce(p2, c2)) &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f]crypto_chars(?in_kind, input, length, ?in_ccs) &*&
               // only tags of 16 bytes for simplicity
               chars_(tag, tag_len, _) &*& tag_len == 16 &*&
               chars_(output, length, _); @*/
  /*@ ensures  gcm_context_initialized(ctx, p1, c1) &*&
               // this increment enforces a fresh IV on each invocation
               random_permission(p2, c2 + 1) &*&
               // content of updated iv is correlated with input
               crypto_chars(join_kinds(iv_kind, in_kind), iv, iv_len, _) &*&
               [f]crypto_chars(in_kind, input, length, in_ccs) &*&
               crypto_chars(?out_kind, tag, tag_len, ?tag_ccs) &*&
               crypto_chars(out_kind, output, length, ?out_ccs) &*&
               result != 0 ?
                 // encryption not successful
                 out_kind == join_kinds(iv_kind, in_kind)
               :
                 // encryption was successful
                 out_kind == secret &*&
                 exists(?enc_cg) &*& cg_is_gen_or_pub(enc_cg) &&
                 append(tag_ccs, out_ccs) == ccs_for_cg(enc_cg) &*&
                 enc_cg == cg_aes_auth_encrypted(p1, c1, in_ccs, iv_ccs); @*/

int gcm_auth_decrypt(gcm_context *ctx, size_t length,
                     const char *iv, size_t iv_len,
                     const char *add, size_t add_len,
                     const char *tag, size_t tag_len,
                     const char *input, char *output);
  /*@ requires gcm_context_initialized(ctx, ?p1, ?c1) &*&
               // iv_len must be 16 since only AES is supported (see gcm_init)
               crypto_chars(?iv_kind, iv, iv_len, ?iv_ccs) &*& iv_len == 16 &*&
               // no additional data supported yet
               add == NULL &*& add_len == 0 &*&
               [?f1]crypto_chars(?in_kind, tag, tag_len, ?tag_ccs) &*&
                 tag_len == 16 &*&
               [?f2]crypto_chars(in_kind, input, length, ?in_ccs) &*&
               exists(?in_cg) &*&
               append(tag_ccs, in_ccs) == ccs_for_cg(in_cg) &*&
               in_cg == cg_aes_auth_encrypted(?p2, ?c2, ?out_ccs2, ?iv_ccs2) &*&
               chars_(output, length, _); @*/
  /*@ ensures  gcm_context_initialized(ctx, p1, c1) &*&
               [f1]crypto_chars(in_kind, tag, tag_len, tag_ccs) &*&
               [f2]crypto_chars(in_kind, input, length, in_ccs) &*&
               crypto_chars(?out_kind, output, length, ?out_ccs) &*&
               // content of updated iv is correlated with output
               crypto_chars(join_kinds(iv_kind, out_kind), iv, iv_len, _) &*&
               result != 0 ?
                 out_kind == join_kinds(iv_kind, in_kind)
               :
                 out_kind == secret &*&
                 col || (p1 == p2 && c1 == c2 && iv_ccs == iv_ccs2 &&
                         out_ccs == out_ccs2); @*/

#endif
