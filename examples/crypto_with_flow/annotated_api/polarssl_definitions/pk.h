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
                [?f1]crypto_chars(?kind, input, ilen, ?cs_input) &*&
                  ilen >= MINIMAL_STRING_SIZE &*&
                  // encrypted message can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, input, ilen, cs_input) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p2, c2 + 1) &*&
                result != 0 ?
                  // encryption failed
                  chars(output, osize, _)
                :
                  exists(?cg) &*& cg == cg_asym_encrypted(p1, c1, cs_input, _) &*&
                  olen_val > 0 &*& olen_val <= osize &*&
                  8 * olen_val <= nbits &*&
                  cg == cg_asym_encrypted(p1, c1, cs_input, _) &*&
                  chars(output + olen_val, osize - olen_val, _) &*&
                  kind == garbage ?
                    // got garbage as input
                    crypto_chars(garbage, output, osize, chars_for_cg(cg))
                  : 
                    // encryption was successful
                    cryptogram(output, olen_val, _, cg); @*/

int pk_decrypt(pk_context *ctx, const char *input, size_t ilen, char *output,
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_private, ?p1, ?c1, ?nbits) &*&
                [?f1]cryptogram(input, ilen, ?cs_input, ?cg_input) &*&
                  cg_input == cg_asym_encrypted(?p2, ?c2, ?cs_output, _) &*&
                  ilen >= MINIMAL_STRING_SIZE &*&
                  // message to decrypt can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p3, ?c3); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p1, c1, nbits) &*&
                [f1]cryptogram(input, ilen, cs_input, cg_input) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p3, c3 + 1) &*&
                result != 0 ?
                  chars(output, osize, _)
                : 
                (
                  olen_val > 0 &*& olen_val <= osize &*&
                  chars(output + olen_val, osize - olen_val, _) &*&
                  col || p1 != p2 || c1 != c2 ?
                    crypto_chars(garbage, output, olen_val, cs_output) &*&
                    true == decrypted_garbage(cs_output)
                  :
                    crypto_chars(secret, output, olen_val, cs_output)
                ); @*/

int pk_sign(pk_context *ctx, int md_alg, const char *hash, size_t hash_len,
            char *sig, size_t *sig_len, void *f_rng, void *p_rng);
  /*@ requires  pk_context_with_key(ctx, pk_private, ?p1, ?c1, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f1]crypto_chars(?kind, hash, hash_len, ?cs_input) &*&
                  hash_len >= MINIMAL_STRING_SIZE &*&
                  // hash to sign can not be bigger than key
                  hash_len * 8 <= nbits &*&
                u_integer(sig_len, _) &*&
                chars(sig, ?out_len, _) &*& 8 * out_len >= nbits &*&
                random_state_predicate(?state_pred) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                principal(?p2, ?c2); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_private, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, hash, hash_len, cs_input) &*&
                u_integer(sig_len, ?sig_len_val) &*&
                [f2]state_pred(p_rng) &*&
                principal(p2, c2 + 1) &*&
                result != 0 ?
                  // signing failed
                  chars(sig, out_len, _)
                :
                  exists(?cg) &*& cg == cg_asym_signature(p1, c1, cs_input, _) &*&
                  sig_len_val > 0 &*& sig_len_val <= out_len &*&
                  chars(sig + sig_len_val, out_len - sig_len_val, _) &*&
                  kind == garbage ?
                    // got garbage as input
                    crypto_chars(garbage, sig, out_len, chars_for_cg(cg))
                  :
                    // signing was successful
                    cryptogram(sig, sig_len_val, _, cg); @*/

int pk_verify(pk_context *ctx, int md_alg, const char *hash,
              size_t hash_len, const char *sig, size_t sig_len );
  /*@ requires  pk_context_with_key(ctx, pk_public, ?p1, ?c1, ?nbits) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f1]crypto_chars(?kind, hash, hash_len, ?cs_in) &*&
                  hash_len >= MINIMAL_STRING_SIZE &*&
                  // hash to verify can not be bigger than key
                  hash_len * 8 <= nbits &*&
                [?f2]cryptogram(sig, sig_len, ?cs_sig, ?cg_sig) &*&
                  cg_sig == cg_asym_signature(?p2, ?c2, ?cs_in2, _); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, p1, c1, nbits) &*&
                [f1]crypto_chars(kind, hash, hash_len, cs_in) &*&
                [f2]cryptogram(sig, sig_len, cs_sig, cg_sig) &*&
                col || result != 0 ? true :
                  p1 == p2 && c1 == c2 && cs_in == cs_in2; @*/

#endif
