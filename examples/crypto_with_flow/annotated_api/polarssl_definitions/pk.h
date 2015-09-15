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
  context->pk_info |-> ?info &*&
  context->pk_ctx |-> ?ctx &*&
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
  //@ requires pk_type == POLARSSL_PK_RSA;
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
               chars(buf, size, _) &*& nbits == size; @*/ 
  /*@ ensures  pk_context_with_keys(ctx, p, c, nbits, info) &*&
               result == 0 ?
                 cryptogram(buf, size, ?key_cs, ?key) &*&
                 key == cg_public_key(p, c) &*&
                 info == cg_info(key)
               :
                 chars(buf, size, _); 
  @*/

int pk_write_key_pem(pk_context *ctx, char *buf, size_t size);
  /*@ requires pk_context_with_keys(ctx, ?p, ?c, ?nbits, ?info) &*&
               //To fix size and to ensure that there is enough space.
               chars(buf, size, _) &*&  nbits == size; @*/
  /*@ ensures  pk_context_with_keys(ctx, p, c, nbits, info) &*&
               result == 0 ?
                 cryptogram(buf, size, ?key_cs, ?key) &*&
                 key == cg_private_key(p, c) &*&
                 info == cg_info(key)
               :
                 chars(buf, size, _); 
  @*/

/*@
lemma void pk_info_for_keypair(int principal, int count);
  requires true;
  ensures  cg_info(cg_public_key(principal, count)) ==
           cg_info(cg_private_key(principal, count));
@*/

int pk_parse_public_key(pk_context *ctx, const char *key, size_t keylen);
  /*@ requires pk_context_initialized(ctx) &*&
               [?f]cryptogram(key, keylen, ?cs_key, ?cg_key) &*&
               cg_key == cg_public_key(?p, ?c); @*/
  /*@ ensures  [f]cryptogram(key, keylen, cs_key, cg_key) &*&
               result == 0 ?
                 pk_context_with_key(ctx, pk_public, p, c, keylen)
               :
                 pk_context_garbage(ctx); @*/
  
int pk_parse_key(pk_context *ctx, const char *key, size_t keylen,
                                  const char *pwd, size_t pwdlen);
  /*@ requires pk_context_initialized(ctx) &*&
               pwd == NULL &*& pwdlen == 0 &*&
               [?f]cryptogram(key, keylen, ?cs_key, ?cg_key) &*&
               cg_key == cg_private_key(?p, ?c); @*/
  /*@ ensures  [f]cryptogram(key, keylen, cs_key, cg_key) &*&
               result == 0 ?
                 pk_context_with_key(ctx, pk_private, p, c, keylen)
               :
                 pk_context_garbage(ctx); @*/
  
int pk_encrypt(pk_context *ctx, const char *input, size_t ilen, char *output, 
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_public, ?p1, ?c1, ?nbits) &*&
                [?f1]optional_crypto_chars(?cc, input, ilen, ?cs_input) &*&
                  ilen >= MIN_ENC_SIZE &*&
                  // encrypted message can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p1, c1, nbits) &*&
                [f1]optional_crypto_chars(cc, input, ilen, cs_input) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p2, c2 + 1) &*&
                result == 0 ?
                  olen_val > 0 &*& olen_val <= osize &*&
                  8 * olen_val <= nbits &*&
                  cryptogram(output, olen_val, ?cs_out, ?cg_out) &*&
                  cg_out == cg_asym_encrypted(p1, c1, cs_input, _) &*&
                  chars(output + olen_val, osize - olen_val, _)
                :
                  chars(output, osize, _); @*/

int pk_decrypt(pk_context *ctx, const char *input, size_t ilen, char *output, 
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_private, ?p1, ?c1, ?nbits) &*&
                [?f1]optional_crypto_chars(?cc, input, ilen, ?cs_input) &*&
                  ilen >= MIN_ENC_SIZE &*&
                  // message to decrypt can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p1, c1, nbits) &*&
                [f1]optional_crypto_chars(cc, input, ilen, cs_input) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p2, c2 + 1) &*&
                result == 0 ?
                  olen_val > 0 &*& olen_val <= osize &*&
                  collision_in_run ?
                    chars(output, osize, _)
                  :
                    crypto_chars(output, olen_val, ?cs_output) &*&
                    chars(output + olen_val, osize - olen_val, _) &*&
                    [_]exists(?ent) &*&
                    collision_in_run ||
                    cs_input == chars_for_cg(
                                  cg_asym_encrypted(p1, c1, cs_output, ent))
                :
                  chars(output, osize, _); @*/

int pk_sign(pk_context *ctx, int md_alg, const char *hash, size_t hash_len,
            char *sig, size_t *sig_len, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_private, ?p1, ?c1, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f1]optional_crypto_chars(?cc, hash, hash_len, ?cs_input) &*&
                  hash_len >= MIN_HMAC_INPUT_SIZE &*&
                  // hash to sign can not be bigger than key
                  hash_len * 8 <= nbits &*&
                u_integer(sig_len, _) &*&
                chars(sig, ?out_len, _) &*& 8 * out_len >= nbits &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p1, c1, nbits) &*&
                [f1]optional_crypto_chars(cc, hash, hash_len, cs_input) &*&
                u_integer(sig_len, ?sig_len_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p2, c2 + 1) &*&
                result == 0 ?
                  sig_len_val > 0 &*& sig_len_val <= out_len &*& 
                  cryptogram(sig, sig_len_val, ?cs_out, ?cg_output) &*&
                  chars(sig + sig_len_val, out_len - sig_len_val, _) &*&
                  cg_output == cg_asym_signature(p1, c1, cs_input, _)
                :
                  chars(sig, out_len, _); @*/

int pk_verify(pk_context *ctx, int md_alg, const char *hash, 
              size_t hash_len, const char *sig, size_t sig_len );
  /*@ requires  pk_context_with_key(ctx, pk_public, ?p, ?c, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f1]optional_crypto_chars(?cc1, hash, hash_len, ?cs_input) &*&
                  hash_len >= MIN_ENC_SIZE &*&
                  // hash to verify can not be bigger than key
                  hash_len * 8 <= nbits &*&
                [?f2]optional_crypto_chars(?cc2, sig, sig_len, ?cs_sig); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p, c, nbits) &*&
                [f1]optional_crypto_chars(cc1, hash, hash_len, cs_input) &*&
                [f2]optional_crypto_chars(cc2, sig, sig_len, cs_sig) &*&
                result == 0 ?
                  exists(?ent) &*&
                  collision_in_run ||
                  cs_sig == chars_for_cg(cg_asym_signature(p, c, cs_input, ent))
                :
                  true; @*/

#endif