#ifndef POLARSSL_H
#define POLARSSL_H

#include "shared_definitions.h"
#include "aux_include/polarssl_sizes.h"

#define AES_ENCRYPT   1
#define AES_DECRYPT   0

///////////////////////////////////////////////////////////////////////////////
// PolarSSL Principals ////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate polarssl_principal(int p);

predicate polarssl_principals(int count);

predicate polarssl_initial_principals() =
      polarssl_principals(0);

predicate polarssl_generated_values(int principal, int count);

@*/

/*@

lemma void create_polarssl_principal<T>(int count);
  requires [?f]polarssl_world<T>(?pub) &*&
           polarssl_principals(count);
  ensures  [f]polarssl_world<T>(pub) &*& 
           polarssl_principal(count + 1) &*&
           polarssl_generated_values(count + 1, 0) &*&
           polarssl_principals(count + 1);

lemma void destroy_polarssl_principal<T>(int count);
  requires [?f]polarssl_world<T>(?pub) &*&
           polarssl_principal(count) &*&
           polarssl_generated_values(count, _);
  ensures  [f]polarssl_world<T>(pub);

@*/

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate polarssl_world<T>(fixpoint(T, list<char>, bool) pub);

predicate polarssl_witness<T>(T witness) = true;

lemma void polarssl_init<T>();
  requires exists<fixpoint(T witness, list<char>, bool)>(?pub);
  ensures  polarssl_world<T>(pub) &*&
           polarssl_initial_principals();

lemma void polarssl_exit<T>();
  requires polarssl_world<T>(?pub) &*&
           polarssl_principals(?count);
  ensures  true;

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL Item //////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

inductive polarssl_item =
  | polarssl_havege_item(int principal, int count)
  | polarssl_sha512_item(list<char> key, list<char> payload)
  | polarssl_aes_encrypted_item(list<char> key, int iv_offset, list<char> iv, 
                                list<char> payload)
  | polarssl_rsa_public_key_item(int principal, int count)
  | polarssl_rsa_private_key_item(int principal, int count)
  | polarssl_rsa_encrypted_item(int principal, int count,
                                list<char> payload, list<char> entropy)
;

predicate polarssl_item(void *item; polarssl_item i);

fixpoint int info_for_polarssl_item(polarssl_item i);

@*/

///////////////////////////////////////////////////////////////////////////////
// Random number generation - see "havege.h" //////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct havege_state
{
  char content[CHAR_SIZE_OF_HAVEGE_STATE];
};
typedef struct havege_state havege_state;

/*@

predicate havege_state(havege_state *state) =
  chars((void*) state, CHAR_SIZE_OF_HAVEGE_STATE, _) &*&
  struct_havege_state_padding(state)
;

predicate havege_state_initialized(havege_state *state);

predicate havege_request(int principal, int info) = true;

fixpoint list<char> havege_chars_for_polarssl_item(polarssl_item i);

lemma void havege_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i  == polarssl_havege_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == havege_chars_for_polarssl_item(i);

lemma void havege_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i  == polarssl_havege_item(_, _) &*&
           cs == havege_chars_for_polarssl_item(i);

lemma void havege_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                       polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_havege_item(_, _) &*&
           i2 == polarssl_havege_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (havege_chars_for_polarssl_item(i1) == 
                  havege_chars_for_polarssl_item(i2)));

@*/

void havege_init/*@ <T> @*/(havege_state *havege_state);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               havege_state(havege_state); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               havege_state_initialized(havege_state); @*/

/*@
lemma void havege_exit<T>(havege_state *havege_state);
      requires [?f]polarssl_world<T>(?pub) &*&
               havege_state_initialized(havege_state);
      ensures  [f]polarssl_world<T>(pub) &*&
               havege_state(havege_state);
@*/

int havege_random/*@ <T> @*/(void *havege_state, char *output, size_t len);
  /*@ requires
        [?f0]polarssl_world<T>(?pub) &*&
        [?f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(?principal, ?count) &*&
        havege_request(principal, ?info) &*&
        chars(output, len, _);
  @*/
  /*@ ensures
        [f0]polarssl_world<T>(pub) &*&
        [f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(principal, count + 1) &*&
        polarssl_item(output, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Signing - see "sha512.h" ///////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint list<char> sha512_chars_for_polarssl_item(polarssl_item i);

lemma void sha512_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i  == polarssl_sha512_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == sha512_chars_for_polarssl_item(i);

lemma void sha512_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i  == polarssl_sha512_item(_, _) &*&
           cs == sha512_chars_for_polarssl_item(i);
 
lemma void sha512_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                       polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_sha512_item(_, _) &*&
           i2 == polarssl_sha512_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (sha512_chars_for_polarssl_item(i1) == 
                  sha512_chars_for_polarssl_item(i2)));
@*/

void sha512_hmac/*@ <T> @*/(const char *key, size_t keylen,
                            const char *input, size_t ilen,
                            char *output, int is384);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*&
               chars(key, keylen, ?cs_key) &*& chars(input, ilen, ?cs_pay) &*&
               chars(output, ?length, _) &*& (is384 == 0 || is384 == 1) &*&
               is384 == 0 ? length == 64 : length == 48; @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*&
               chars(key, keylen, cs_key) &*& chars(input, ilen, cs_pay) &*&
               polarssl_item(output, ?i) &*&
               i == polarssl_sha512_item(cs_key, cs_pay) &*& 
               length == length(sha512_chars_for_polarssl_item(i)); @*/

///////////////////////////////////////////////////////////////////////////////
// Symmetric encryption - see "aes.h" /////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct aes_context
{
  char content[CHAR_SIZE_OF_AES_CONTEXT];
};
typedef struct aes_context aes_context;

/*@

predicate aes_context(aes_context *context) =
  chars((void*) context, CHAR_SIZE_OF_AES_CONTEXT, _) &*&
  struct_aes_context_padding(context)
;
predicate aes_context_initialized(aes_context *context, list<char> key);

fixpoint list<char> aes_chars_for_polarssl_item(polarssl_item i);

lemma void aes_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i == polarssl_aes_encrypted_item(_, _, _, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == aes_chars_for_polarssl_item(i);

lemma void aes_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i == polarssl_aes_encrypted_item(_, _, _, _) &*&
           cs == aes_chars_for_polarssl_item(i);
 
lemma void aes_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                    polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_aes_encrypted_item(_, _, _, _) &*&
           i2 == polarssl_aes_encrypted_item(_, _, _, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (aes_chars_for_polarssl_item(i1) == 
                  aes_chars_for_polarssl_item(i2)));

@*/

int aes_setkey_enc/*@ <T> @*/(aes_context *ctx, 
                              const char *key, unsigned int keysize);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               chars(key, ?l_key, ?cs_key) &*&
               aes_context(ctx) &*&
               (l_key == 128 || l_key == 192 || l_key == 256); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               chars(key, l_key, cs_key) &*&
               aes_context_initialized(ctx, cs_key); @*/

/*@
lemma void aes_release_context<T>(aes_context *ctx);
      requires [?f]polarssl_world<T>(?pub) &*&
               aes_context_initialized(ctx, ?cs_key);
      ensures  [f]polarssl_world<T>(pub) &*&
               aes_context(ctx);
@*/

int aes_crypt_cfb128/*@ <T> @*/(aes_context *ctx, int mode, size_t length, 
                                size_t *iv_off, char *iv, 
                                const char *input, char *output);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
        aes_context_initialized(ctx, ?cs_key) &*&
        chars(iv, 16, ?cs_iv) &*& u_integer(iv_off, ?iv_off_val) &*&
        iv_off_val >= 0 &*& iv_off_val < 16 &*&
        mode == AES_ENCRYPT ?
        (
          chars(input, length, ?cs_input) &*&
          chars(output, length, _) &*& ensures
          (
            [f]polarssl_world<T>(pub) &*&
            aes_context_initialized(ctx, cs_key) &*&
            chars(input, length, cs_input) &*&
            chars(iv, 16, _) &*& u_integer(iv_off, _) &*&
            polarssl_item(output, ?i) &*&
            i == polarssl_aes_encrypted_item(cs_key, iv_off_val, 
                                             cs_iv, cs_input) &*& 
            length == length(aes_chars_for_polarssl_item(i))
          )
        ) :
        mode == AES_DECRYPT ?
        (
          polarssl_item(input, ?i) &*&
          i == polarssl_aes_encrypted_item(?cs_key', ?iv_off_val', 
                                           ?cs_iv', ?cs_enc) &*& 
          chars(output, length, _) &*& ensures
          (
            [f]polarssl_world<T>(pub) &*&
            aes_context_initialized(ctx, cs_key) &*&
            polarssl_item(input, i) &*&
            chars(iv, 16, _) &*& u_integer(iv_off, _) &*& 
            chars(output, length, ?cs_out) &*&
            true ==
              (
                cs_key     == cs_key' &&
                iv_off_val == iv_off_val' &&
                cs_iv      == cs_iv'
              )
            ?
              cs_out == cs_enc
            :
              // A better contract here would be:
              //   cs_out == cs_enc ? collision_in_run() == true : true
              // or just
              //   true (you can prove collision_in_run() == true yourself)
              //
              // However this would give no info at all about the resulting char 
              // buffer. And so the contract of decrypt would have to say:
              //  true == if_no_collision(
              //       key0 == key_i ? pay0 == result_i : true
              //  ); 
              // in stead of:
              //  true == if_no_collision(
              //       key0 == key_i && pay0 == result_i
              //  );
              // So after decryption with the wrong key, you have no info at all
              // about the item that you get. In which case the attacker also
              // has no information and the pub predicate must be true for all
              // items.
              //
              // Possible solutions:
              //   1) introduce garbage item as the result of incorrect decryption
              //     => does NOT work because it needs a tag and injectivity of items gets lost
              //   2) also encrypt the key, and check after decryption that the key was correct
              //     => seems oke, but very difficult implementation/verification
              //   
              // Remark: this solution is equally strong as the one where our unimplemented decrypt function "aborted"
              //         -in the old solution:
              //          + an attacker could not decrypt with an invalid key without aborting 
              //          + protocols are proven to be correct on the condition that no collision occured
              //         -in the new solution:
              //          + an attacker can decrypt with an invalid key without aborting (= stronger attacker) 
              //          + an attacker can force a collision by faulty decryption 
              //          + protocols are proven to be correct on the condition that no collision occured (= weaker guarantees)
              //
              //         -it seems that both models are equivalent
              collision_in_run() == true
          )
        ) : false; @*/
  //@ ensures emp;

///////////////////////////////////////////////////////////////////////////////
// Asymmetric encryption - see "pk.h" and "rsa.h" /////////////////////////////
///////////////////////////////////////////////////////////////////////////////

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
  malloc_block_pk_context(context)
;

predicate pk_context_initialized(pk_context *context);

predicate pk_info(pk_info_t *info);

predicate pk_context_initialized2(pk_context *context, void *subctx);

inductive pk_kind =
  | pk_public
  | pk_private
;

predicate pk_context_with_key(pk_context *context, int principal, 
                               int count, pk_kind kind);

predicate pk_context_with_keys(pk_context *context, int principal, 
                               int count, int info);

predicate pk_context_garbage(pk_context *context);

predicate rsa_key_request(int principal, int info) = emp;
@*/

void pk_init/*@ <T> @*/(pk_context *ctx);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               pk_context(ctx); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               pk_context_initialized(ctx); @*/

const pk_info_t *pk_info_from_type/*@ <T> @*/(int pk_type);
  //@ requires [?f]polarssl_world<T>(?pub) &*& pk_type == PK_RSA_TYPE;
  //@ ensures  [f]polarssl_world<T>(pub) &*& pk_info(result);
  
int pk_init_ctx/*@ <T> @*/(pk_context *ctx, const pk_info_t *info);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               pk_context_initialized(ctx) &*&
               pk_info(info); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               pk_context_initialized2(ctx, ?subctx) &*& 
               ctx->pk_ctx |-> subctx; @*/
/*@
lemma void pk_release_context_ititialized(pk_context *ctx);
  requires pk_context_initialized(ctx);
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_ititialized2(pk_context *ctx);
  requires pk_context_initialized2(ctx, ?subctx) &*& 
           ctx->pk_ctx |-> subctx;
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_with_key(pk_context *ctx);
  requires pk_context_with_key(ctx, _, _, _);
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_with_keys(pk_context *ctx);
  requires pk_context_with_keys(ctx, _, _, _);
  ensures  pk_context_garbage(ctx);
@*/

void pk_free/*@ <T> @*/(pk_context *ctx);
/*@ requires [?f]polarssl_world<T>(?pub) &*&
             pk_context_garbage(ctx); @*/
/*@ ensures  [f]polarssl_world<T>(pub) &*&
             pk_context(ctx);  @*/

typedef int random_function/*@ <T> @*/(void* state, char* buff, size_t len);
  /*@ requires
        [?f0]polarssl_world<T>(?pub) &*&
        [?f1]havege_state_initialized(state) &*&
        polarssl_generated_values(?principal, ?count) &*&
        havege_request(principal, ?info) &*&
        chars(buff, len, _);
  @*/
  /*@ ensures
        [f0]polarssl_world<T>(pub) &*&
        [f1]havege_state_initialized(state) &*&
        polarssl_generated_values(principal, count + 1) &*&
        polarssl_item(buff, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i); @*/

int rsa_gen_key/*@ <T> @*/(void *ctx, void *f_rng, void *p_rng,
                unsigned int nbits, int exponent);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               pk_context_initialized2(?pk_context, ctx) &*&
               pk_context->pk_ctx |-> ctx &*&
               rsa_key_request(?principal, ?info) &*&
               [_]is_random_function<T>(f_rng) &*&
               [?f1]havege_state_initialized(p_rng) &*&
               nbits >= 1024 && nbits <= 8192 &*& exponent == 65537 &*&
               polarssl_generated_values(principal, ?count); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               [f]havege_state_initialized(p_rng) &*&
               polarssl_generated_values(principal, count + 1) &*&
               pk_context_with_keys(pk_context,
                                    principal, count + 1, info); @*/

/*@
fixpoint list<char> rsa_public_key_chars_for_polarssl_item(polarssl_item i);
fixpoint list<char> rsa_private_key_chars_for_polarssl_item(polarssl_item i);
fixpoint list<char> rsa_encrypted_chars_for_polarssl_item(polarssl_item i);

lemma void rsa_public_key_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_public_key_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == rsa_public_key_chars_for_polarssl_item(i);

lemma void rsa_public_key_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_public_key_item(_, _) &*&
           cs == rsa_public_key_chars_for_polarssl_item(i);

lemma void rsa_public_key_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                               polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_rsa_public_key_item(_, _) &*&
           i2 == polarssl_rsa_public_key_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (rsa_public_key_chars_for_polarssl_item(i1) == 
                  rsa_public_key_chars_for_polarssl_item(i2)));

lemma void rsa_private_key_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_private_key_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == rsa_private_key_chars_for_polarssl_item(i);

lemma void rsa_private_key_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_private_key_item(_, _) &*&
           cs == rsa_private_key_chars_for_polarssl_item(i);

lemma void rsa_private_key_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                               polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_rsa_private_key_item(_, _) &*&
           i2 == polarssl_rsa_private_key_item(_, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (rsa_private_key_chars_for_polarssl_item(i1) == 
                  rsa_private_key_chars_for_polarssl_item(i2)));

lemma void rsa_encrypted_polarssl_item_to_chars<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_encrypted_item(_, _, _, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]chars(item, ?length, ?cs) &*&
           cs == rsa_encrypted_chars_for_polarssl_item(i);

lemma void rsa_encrypted_chars_to_polarssl_item<T>(void* item);
  requires [?f0]polarssl_world<T>(?pub) &*&
           [?f1]chars(item, ?length, ?cs);
  ensures  [f0]polarssl_world<T>(pub) &*&
           [f1]polarssl_item(item, ?i) &*&
           i  == polarssl_rsa_encrypted_item(_, _, _, _) &*&
           cs == rsa_encrypted_chars_for_polarssl_item(i);

lemma void rsa_encrypted_chars_for_polarssl_item_injective<T>(polarssl_item i1,
                                                              polarssl_item i2);
  requires [?f0]polarssl_world<T>(?pub) &*&
           i1 == polarssl_rsa_encrypted_item(_, _, _, _) &*&
           i2 == polarssl_rsa_encrypted_item(_, _, _, _);
  ensures  [f0]polarssl_world<T>(pub) &*&
           collision_in_run() ? true : true == 
                 ((i1 == i2) 
               == 
                 (rsa_encrypted_chars_for_polarssl_item(i1) == 
                  rsa_encrypted_chars_for_polarssl_item(i2)));

@*/

int pk_write_pubkey_pem/*@ <T> @*/(pk_context *ctx, char *buf, size_t size);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               chars(buf, size, _) &*&
               pk_context_with_keys(ctx, ?principal, ?count, ?info); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               pk_context_with_keys(ctx, principal, count, info) &*&
               result == 0 ?
                 polarssl_item(buf, ?key) &*&
                 key == polarssl_rsa_public_key_item(principal, count) &*&
                 info == info_for_polarssl_item(key) &*&
                 size == length(rsa_public_key_chars_for_polarssl_item(key))
               :
                 chars(buf, size, _); 
  @*/

int pk_parse_public_key/*@ <T> @*/(pk_context *ctx,
                                   const unsigned char *key, size_t keylen);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               pk_context_initialized(ctx) &*&
               polarssl_item(key, ?kkey) &*&
                 kkey == polarssl_rsa_public_key_item(?principal, ?count) &*&
                 keylen == length(rsa_public_key_chars_for_polarssl_item(kkey));
  @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               polarssl_item(key, kkey) &*&
               result == 0 ?
                 pk_context_with_key(ctx, principal, count, pk_public)
               :
                 pk_context_garbage(ctx); @*/

int pk_write_key_pem/*@ <T> @*/(pk_context *ctx, char *buf, size_t size);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               chars(buf, size, _) &*&
               pk_context_with_keys(ctx, ?principal, ?count, ?info); @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               pk_context_with_keys(ctx, principal, count, info) &*&
               result == 0 ?
                 polarssl_item(buf, ?key) &*&
                 key == polarssl_rsa_private_key_item(principal, count) &*&
                 info == info_for_polarssl_item(key) &*&
                 size == length(rsa_private_key_chars_for_polarssl_item(key))
               : 
                 chars(buf, size, _); 
  @*/

int pk_parse_key/*@ <T> @*/(pk_context *ctx,
                            const unsigned char *key, size_t keylen,
                            const unsigned char *pwd, size_t pwdlen);
  /*@ requires [?f]polarssl_world<T>(?pub) &*&
               pk_context_initialized(ctx) &*&
               pwd == 0 &*& pwdlen == 0 &*&
               polarssl_item(key, ?kkey) &*&
                 kkey == polarssl_rsa_private_key_item(?principal, ?count) &*&
                 keylen == length(rsa_private_key_chars_for_polarssl_item(kkey));
  @*/
  /*@ ensures  [f]polarssl_world<T>(pub) &*&
               polarssl_item(key, kkey) &*&
               result == 0 ?
                 pk_context_with_key(ctx, principal, count, pk_private)
               :
                 pk_context_garbage(ctx); @*/

int pk_encrypt/*@ <T> @*/(pk_context *ctx,
                          const char *input, size_t ilen,
                          char *output, size_t *olen, size_t osize,
                          void *f_rng, void *p_rng);
  /*@ requires  [?f0]polarssl_world<T>(?pub) &*&
                pk_context_with_key(ctx, ?principal1, ?count1, pk_public) &*&
                chars((void*) input, ilen, ?cs_in) &*&
                u_integer(olen, _) &*&
                chars((void*) output, osize, ?cs_out) &*&
                [_]is_random_function<T>(f_rng) &*&
                [?f1]havege_state_initialized(p_rng) &*&
                polarssl_generated_values(?principal2, ?count2); @*/
  /*@ ensures   [f0]polarssl_world<T>(pub) &*&
                pk_context_with_key(ctx, principal1, count1, pk_public) &*&
                chars((void*) input, ilen, cs_in) &*&
                u_integer(olen, ?olen_val) &*&
                [f1]havege_state_initialized(p_rng) &*&
                polarssl_generated_values(principal2, count2 + 1) &*&
                result == 0 ?
                    polarssl_item(output, ?pi) &*& 
                    pi == polarssl_rsa_encrypted_item(principal1, 
                                            count1, cs_in, ?entropy) &*&
                    olen_val == length(
                                 rsa_encrypted_chars_for_polarssl_item(pi)) &*&
                    chars((void*) output + olen_val, osize - olen_val, _)
                :
                    chars((void*) output, osize, _)
                ; @*/

int pk_decrypt/*@ <T> @*/(pk_context *ctx,
                          const char *input, size_t ilen,
                          char *output, size_t *olen, size_t osize,
                          void *f_rng, void *p_rng);
  /*@ requires  [?f0]polarssl_world<T>(?pub) &*&
                pk_context_with_key(ctx, ?principal1, ?count1, pk_private) &*&
                polarssl_item(input, ?pi) &*& 
                    pi == polarssl_rsa_encrypted_item(?principal2,
                                            ?count2, ?cs_enc, ?entropy) &*&
                ilen == length(chars_for_polarssl_item(pi)) &*&
                u_integer(olen, _) &*&
                chars((void*) output, osize, ?cs_out) &*&
                [_]is_random_function<T>(f_rng) &*&
                [?f1]havege_state_initialized(p_rng) &*&
                polarssl_generated_values(?principal3, ?count3); @*/
  /*@ ensures   [f0]polarssl_world<T>(pub) &*&
                pk_context_with_key(ctx, principal1, count1, pk_private) &*&
                polarssl_item(input, pi) &*&
                u_integer(olen, ?olen_val) &*&
                [f1]havege_state_initialized(p_rng) &*&
                polarssl_generated_values(principal3, count3 + 1) &*&
                result == 0 ?
                  (
                    principal1 == principal2 && count1 == count2 ?
                      chars((void*) output, olen_val, cs_enc) &*&
                      chars((void*) output + olen_val, osize - olen_val, _) &*&
                      olen_val == length(cs_enc)
                    :
                      // see explenation in contract for aes_crypt_cfb128
                      chars((void*) output, osize, _) &*&
                      collision_in_run() == true
                  )
                :
                  chars((void*) output, osize, _)
                ; @*/
    
///////////////////////////////////////////////////////////////////////////////
// Networking - see "net.h" ///////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

fixpoint list<char> chars_for_polarssl_item(polarssl_item i)
{
  switch (i)
  {
    case polarssl_havege_item(p, c): 
      return havege_chars_for_polarssl_item(i);
    case polarssl_sha512_item(k, p):
      return sha512_chars_for_polarssl_item(i);
    case polarssl_aes_encrypted_item(k, iv_off, iv_cs, p):
      return aes_chars_for_polarssl_item(i);
    case polarssl_rsa_public_key_item(p, c):
      return rsa_public_key_chars_for_polarssl_item(i);
    case polarssl_rsa_private_key_item(p, c):
      return rsa_private_key_chars_for_polarssl_item(i);      
    case polarssl_rsa_encrypted_item(p, info, pay, ent):
      return rsa_encrypted_chars_for_polarssl_item(i);
  }
}

inductive socket_status =
 | bound_to_port
 | connection_init
 | connected
;

predicate polarssl_net_status(int socket, list<char> socket_ip, 
                              int socket_port, socket_status socket_stat);
@*/

int net_connect/*@ <T> @*/(int *fd, const char *host, int port);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*&
               integer(fd, _) &*& [?f1]string(host, ?s_ip); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*&
               integer(fd, ?s_fd) &*& [f1]string(host, s_ip) &*&
               result == 0 ?
                   polarssl_net_status(s_fd, s_ip, port, connection_init)
                 :
                   true; @*/

int net_set_block/*@ <T> @*/(int fd);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*&
               polarssl_net_status(?s_fd, ?s_ip, ?port, connection_init); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*&
               result == 0 ?
                   polarssl_net_status(s_fd, s_ip, port, connected) 
                 :
                   true; @*/

int net_bind/*@ <T> @*/(int *fd, const char *bind_ip, int port);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*&
               integer(fd, _) &*& chars(bind_ip, ?len, ?s_ip); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*&
               integer(fd, ?s_fd) &*& chars(bind_ip, len, s_ip) &*&
               result == 0 ?
                   polarssl_net_status(s_fd, s_ip, port, bound_to_port)
                 :
                   true; @*/

int net_accept/*@ <T> @*/(int bind_fd, int *client_fd, void *client_ip);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*&
               integer(client_fd, _) &*& chars(client_ip, ?c_len, ?c_ip) &*& 
               polarssl_net_status(bind_fd, ?ip, ?port, bound_to_port); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*&
               integer(client_fd, ?c_fd) &*& chars(client_ip, c_len, c_ip) &*& 
               polarssl_net_status(bind_fd, ip, port, bound_to_port) &*&
               result == 0 ?
                   polarssl_net_status(c_fd, c_ip, _, connection_init)
                 :
                   true; @*/
  
void net_usleep/*@ <T> @*/(unsigned long usec);
  //@ requires [?f0]polarssl_world<T>(?pub);
  //@ ensures  [f0]polarssl_world<T>(pub);

int net_recv/*@ <T> @*/(void *ctx, char *buf, size_t len);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*& integer(ctx, ?fd) &*&
               polarssl_net_status(fd, ?ip, ?port, connected) &*&
               chars(buf, len, _); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*& integer(ctx, fd) &*&
               polarssl_net_status(fd, ip, port, connected) &*&
               result < 0 ?
                   chars(buf, len, _)
                 :
                   result <= len &*& 
                   chars(buf, result, ?cs) &*& 
                   chars(buf + result, len - result, _) &*&
                   polarssl_witness<T>(?witness) &*&
                   pub(witness, cs) == true; @*/

int net_send/*@ <T> @*/(void *ctx, const char *buf, size_t len);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*& integer(ctx, ?fd) &*&
               polarssl_net_status(fd, ?ip, ?port, connected) &*&
               chars(buf, len, ?cs) &*& 
               polarssl_witness<T>(?witness) &*&
               (collision_in_run() || pub(witness, cs)); @*/
  /*@ ensures  [f0]polarssl_world<T>(pub) &*& integer(ctx, fd) &*&
               polarssl_net_status(fd, ip, port, connected) &*&
               chars(buf, len, cs); @*/

void net_close/*@ <T> @*/(int fd);
  /*@ requires [?f0]polarssl_world<T>(?pub) &*& 
               polarssl_net_status(fd, _, _, _); @*/
  //@ ensures  [f0]polarssl_world<T>(pub);

#endif
