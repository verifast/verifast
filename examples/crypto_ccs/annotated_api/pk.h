#ifndef POLARSSL_PK_H
#define POLARSSL_PK_H

#include "macro_defines.h"
#include "net.h"
#include "havege.h"

struct pk_info_t;
typedef struct pk_info_t pk_info_t;

struct pk_context
{
  const pk_info_t *pk_info;
  void *pk_ctx;
};
typedef struct pk_context pk_context;

/*@
predicate pk_context(pk_context *context) =
  context->pk_info |-> _ &*&
  context->pk_ctx |-> _ &*&
  struct_pk_context_padding(context)
;

predicate pk_context_initialized(pk_context *context);

predicate pk_info(pk_info_t *info);

predicate pk_context_initialized2(pk_context *context, void *subctx);

inductive pk_kind =
  | pk_public
  | pk_private
;

predicate pk_context_with_key(pk_context *context, pk_kind kind,
                              int principal, int count, int bit_size);

predicate pk_context_with_keys(pk_context *context, int principal,
                               int count, int bit_size, int info);

predicate pk_context_garbage(pk_context *context);

predicate rsa_key_request(int principal, int info) = emp;

@*/

void pk_init(pk_context *ctx);
  //@ requires pk_context(ctx);
  //@ ensures  pk_context_initialized(ctx);

const pk_info_t *pk_info_from_type(int pk_type);
  //@ requires pk_type == MBEDTLS_PK_RSA;
  //@ ensures  pk_info(result);

int pk_init_ctx(pk_context *ctx, const pk_info_t *info);
  /*@ requires pk_context_initialized(ctx) &*&
               pk_info(info); @*/
  /*@ ensures  result == 0 ?
                 pk_context_initialized2(ctx, ?subctx) &*&
                 ctx->pk_ctx |-> subctx
               :
                 pk_context_garbage(ctx); @*/
/*@
lemma void pk_release_context_initialized(pk_context *ctx);
  requires pk_context_initialized(ctx);
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_initialized2(pk_context *ctx);
  requires pk_context_initialized2(ctx, ?subctx) &*&
           ctx->pk_ctx |-> subctx;
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_with_key(pk_context *ctx);
  requires pk_context_with_key(ctx, _, _, _, _);
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_with_keys(pk_context *ctx);
  requires pk_context_with_keys(ctx, _, _, _, _);
  ensures  pk_context_garbage(ctx);
@*/

void pk_free(pk_context *ctx);
/*@ requires pk_context_garbage(ctx); @*/
/*@ ensures  pk_context(ctx);  @*/

int pk_write_pubkey_pem(pk_context *ctx, char *buf, size_t size);
  /*@ requires pk_context_with_keys(ctx, ?p, ?c, ?nbits, ?info) &*&
               //To fix size and to ensure that there is enough space.
               chars_(buf, size, _) &*& nbits == size; @*/
  /*@ ensures  pk_context_with_keys(ctx, p, c, nbits, info) &*&
               result == 0 ?
                 cryptogram(buf, size, ?key_ccs, ?key) &*&
                 key == cg_rsa_public_key(p, c) &*&
                 info == cg_info(key)
               :
                 chars_(buf, size, _);
  @*/

int pk_write_key_pem(pk_context *ctx, char *buf, size_t size);
  /*@ requires pk_context_with_keys(ctx, ?p, ?c, ?nbits, ?info) &*&
               //To fix size and to ensure that there is enough space.
               chars_(buf, size, _) &*&  nbits == size; @*/
  /*@ ensures  pk_context_with_keys(ctx, p, c, nbits, info) &*&
               result == 0 ?
                 cryptogram(buf, size, ?key_ccs, ?key) &*&
                 key == cg_rsa_private_key(p, c) &*&
                 info == cg_info(key)
               :
                 chars_(buf, size, _);
  @*/

/*@
lemma void pk_info_for_keypair(int principal, int count);
  requires true;
  ensures  cg_info(cg_rsa_public_key(principal, count)) ==
           cg_info(cg_rsa_private_key(principal, count));
@*/

int pk_parse_public_key(pk_context *ctx, const char *key, size_t keylen);
  /*@ requires pk_context_initialized(ctx) &*&
               [?f]cryptogram(key, keylen, ?ccs_key, ?cg_key) &*&
               cg_key == cg_rsa_public_key(?p, ?c); @*/
  /*@ ensures  [f]cryptogram(key, keylen, ccs_key, cg_key) &*&
               result == 0 ?
                 pk_context_with_key(ctx, pk_public, p, c, keylen)
               :
                 pk_context_garbage(ctx); @*/

int pk_parse_key(pk_context *ctx, const char *key, size_t keylen,
                                  const char *pwd, size_t pwdlen);
  /*@ requires pk_context_initialized(ctx) &*&
               pwd == NULL &*& pwdlen == 0 &*&
               [?f]cryptogram(key, keylen, ?ccs_key, ?cg_key) &*&
               cg_key == cg_rsa_private_key(?p, ?c); @*/
  /*@ ensures  [f]cryptogram(key, keylen, ccs_key, cg_key) &*&
               result == 0 ?
                 pk_context_with_key(ctx, pk_private, p, c, keylen)
               :
                 pk_context_garbage(ctx); @*/

int pk_encrypt(pk_context *ctx, const char *input, size_t ilen, char *output,
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_public, ?p1, ?c1, ?nbits) &*&
                [?f1]crypto_chars(?kind, input, ilen, ?ccs_input) &*&
                  ilen >= MINIMAL_STRING_SIZE &*&
                  // encrypted message can not be bigger than key
                  ilen * 8 <= nbits &*&
                *olen |-> _ &*&
                chars_(output, osize, _) &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                random_permission(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, input, ilen, ccs_input) &*&
                *olen |-> ?olen_val &*&
                [f2]state_pred(p_rng) &*&
                random_permission(p2, c2 + 1) &*&
                result != 0 ?
                  // encryption failed
                  chars(output, osize, _)
                :
                  // encryption was successful
                  cryptogram(output, olen_val, _, ?cg) &*&
                  olen_val > 0 &*& olen_val <= osize &*&
                  8 * olen_val <= nbits &*&
                  cg == cg_rsa_encrypted(p1, c1, ccs_input, _) &*&
                  chars(output + olen_val, osize - olen_val, _); @*/

int pk_decrypt(pk_context *ctx, const char *input, size_t ilen, char *output,
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  decryption_pre(false, ?garbage_in, ?p1, ?s, ?in_ccs) &*&
                pk_context_with_key(ctx, pk_private, ?p2, ?c2, ?nbits) &*&
                // input
                [?f1]cryptogram(input, ilen, in_ccs, ?cg_input) &*&
                  cg_input == cg_rsa_encrypted(?p3, ?c3, ?ccs_out3, _) &*&
                  // message to decrypt can not be bigger than key
                  ilen * 8 <= nbits &*&
                // output
                *olen |-> _ &*&
                chars_(output, osize, _) &*&
                // entropy
                random_permission(p1, ?c1) &*& 
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p2, c2, nbits) &*&
                [f1]cryptogram(input, ilen, in_ccs, cg_input) &*&
                *olen |-> ?olen_val &*&
                random_permission(p1, c1 + 1) &*&
                [f2]state_pred(p_rng) &*&
                crypto_chars(?kind, output, ?olen_val2, ?ccs_out) &*&
                chars_(output + olen_val2, osize - olen_val2, _) &*&
                decryption_post(false, ?garbage_out, 
                                p1, s, p2, c2, ccs_out) &*&
                garbage_out == (garbage_in || p2 != p3 || c2 != c3) &*&
                result != 0 ?
                  kind == normal
                : 
                  olen_val == olen_val2 &*&
                  garbage_out ?
                    kind == normal
                  :
                    kind == secret &*& ccs_out == ccs_out3; @*/

int pk_sign(pk_context *ctx, int md_alg, const char *hash, size_t hash_len,
            char *sig, size_t *sig_len, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_private, ?p1, ?c1, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == MBEDTLS_MD_NONE &*&
                [?f1]crypto_chars(?kind, hash, hash_len, ?ccs_input) &*&
                  hash_len >= MINIMAL_STRING_SIZE &*&
                  // hash to sign can not be bigger than key
                  hash_len * 8 <= nbits &*&
                *sig_len |-> _ &*&
                chars_(sig, ?out_len, _) &*& 8 * out_len >= nbits &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                random_permission(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, hash, hash_len, ccs_input) &*&
                *sig_len |-> ?sig_len_val &*&
                [f2]state_pred(p_rng) &*&
                random_permission(p2, c2 + 1) &*&
                result != 0 ?
                  // signing failed
                  chars_(sig, out_len, _)
                :
                  // signing was successful
                  cryptogram(sig, sig_len_val, _, ?cg) &*&
                  cg == cg_rsa_signature(p1, c1, ccs_input, _) &*&
                  sig_len_val > 0 &*& sig_len_val <= out_len &*&
                  chars_(sig + sig_len_val, out_len - sig_len_val, _); @*/

int pk_verify(pk_context *ctx, int md_alg, const char *hash,
              size_t hash_len, const char *sig, size_t sig_len );
  /*@ requires  pk_context_with_key(ctx, pk_public, ?p1, ?c1, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == MBEDTLS_MD_NONE &*&
                [?f1]crypto_chars(?kind, hash, hash_len, ?ccs_in) &*&
                  hash_len >= MINIMAL_STRING_SIZE &*&
                  // hash to verify can not be bigger than key
                  hash_len * 8 <= nbits &*&
                [?f2]cryptogram(sig, sig_len, ?ccs_sig, ?cg_sig) &*&
                  cg_sig == cg_rsa_signature(?p2, ?c2, ?ccs_in2, _); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, hash, hash_len, ccs_in) &*&
                [f2]cryptogram(sig, sig_len, ccs_sig, cg_sig) &*&
                col || result != 0 ? true :
                  p1 == p2 && c1 == c2 && ccs_in == ccs_in2; @*/

#endif
