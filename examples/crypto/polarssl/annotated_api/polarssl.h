#ifndef POLARSSL_H
#define POLARSSL_H

#include <stddef.h>
#include <limits.h>
#include <stdbool.h>

#include "polarssl_sizes.h"
//@ #include "auxiliary_definitions.gh"

#define POLARSSL_AES_ENCRYPT   1
#define POLARSSL_AES_DECRYPT   0
#define POLARSSL_GCM_ENCRYPT   1
#define POLARSSL_GCM_DECRYPT   0

///////////////////////////////////////////////////////////////////////////////
// PolarSSL sizes /////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#define POLARSSL_MAX_MESSAGE_BYTE_SIZE     65536

#define POLARSSL_MIN_RANDOM_BYTE_SIZE      4
#define POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE  4
#define POLARSSL_MIN_ENCRYPTED_BYTE_SIZE   4
/*@
fixpoint int polarssl_min_size()
{
  return minimum(cons(POLARSSL_MIN_RANDOM_BYTE_SIZE,
                 cons(POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE,
                 cons(POLARSSL_MIN_ENCRYPTED_BYTE_SIZE,
                      nil))));
}
@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL principals ////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate polarssl_principal(int p);

predicate polarssl_principals(int count);

predicate polarssl_generated_values(int principal, int count);

lemma int polarssl_create_principal();
  requires polarssl_principals(?count);
  ensures  polarssl_principal(count + 1) &*&
           polarssl_generated_values(count + 1, 0) &*&
           polarssl_principals(count + 1) &*&
           result == count + 1;

lemma void polarssl_destroy_principal(int count);
  requires polarssl_principal(count) &*&
           polarssl_generated_values(count, _);
  ensures  true;

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL initialization/finalization ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate polarssl_world(predicate(polarssl_cryptogram) polarssl_pub;);

lemma void polarssl_init();
  requires exists<predicate(polarssl_cryptogram)>(?polarssl_pub);
  ensures  polarssl_world(polarssl_pub) &*& 
           polarssl_principals(0);

lemma void polarssl_exit();
  requires polarssl_world(_) &*& polarssl_principals(_);
  ensures  true;

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL cryptograms ///////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

inductive polarssl_cryptogram =
  | polarssl_random        (int principal, int count)
  | polarssl_symmetric_key (int principal, int count)
  | polarssl_public_key    (int principal, int count)
  | polarssl_private_key   (int principal, int count)
  | polarssl_hash          (list<char> payload)
  | polarssl_hmac          (int principal, int count, list<char> payload)
  | polarssl_encrypted     (int principal, int count, list<char> payload, 
                            list<char> entropy)
  | polarssl_auth_encrypted(int principal, int count, list<char> mac,
                            list<char> payload, list<char> entropy)
  | polarssl_asym_encrypted(int principal, int count,
                            list<char> payload, list<char> entropy)
  | polarssl_asym_signature(int principal, int count,
                            list<char> payload, list<char> entropy)  
;

predicate polarssl_key_id(int principal, int count) = true;

fixpoint int  polarssl_cryptogram_tag(polarssl_cryptogram cg)
{
  switch(cg)
  {
    case polarssl_random(p1, c1):                          return 1;
    case polarssl_symmetric_key(p1, c1):                   return 2;
    case polarssl_public_key(p1, c1):                      return 3;
    case polarssl_private_key(p1, c1):                     return 4;
    case polarssl_hash(cs1):                               return 5;
    case polarssl_hmac(p1, c1, cs1):                       return 6;
    case polarssl_encrypted(p1, c1, cs1, ent1):            return 7;
    case polarssl_auth_encrypted(p1, c1, mac1, cs1, ent1): return 8;
    case polarssl_asym_encrypted(p1, c1, cs1, ent1):       return 9;
    case polarssl_asym_signature(p1, c1, cs1, ent1):       return 10;
  }
}

fixpoint bool polarssl_cryptogram_is_nested(polarssl_cryptogram cg)
{
  switch(cg)
  {
    case polarssl_random(p1, c1):        return false;
    case polarssl_symmetric_key(p1, c1): return false;
    case polarssl_public_key(p1, c1):    return false;
    case polarssl_private_key(p1, c1):   return false;
    default: return true;
  }
}

fixpoint list<char> polarssl_cryptogram_payload(polarssl_cryptogram cg)
{
  switch(cg)
  {
    case polarssl_hash(cs1):                               return cs1;
    case polarssl_hmac(p1, c1, cs1):                       return cs1;
    case polarssl_encrypted(p1, c1, cs1, ent1):            return cs1;
    case polarssl_auth_encrypted(p1, c1, mac1, cs1, ent1): return cs1;
    case polarssl_asym_encrypted(p1, c1, cs1, ent1):       return cs1;
    case polarssl_asym_signature(p1, c1, cs1, ent1):       return cs1;
    default: return nil;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL properties of cryptograms /////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

//Associated information of a cryptogram
fixpoint int polarssl_cryptogram_info(polarssl_cryptogram cg);

//Character representation of a cryptogram
fixpoint list<char> polarssl_chars_for_cryptogram(polarssl_cryptogram cg);

//The minimal set (as a list) of cryptograms exposed by a list of characters
fixpoint list<polarssl_cryptogram> polarssl_cryptograms_in_chars(list<char> cs);

//Is this set (as a list) of cryptograms an upper bound on the cryptograms 
//exposed by a list of characters
fixpoint bool polarssl_cryptograms_in_chars_bound(
                                  list<char> cs, list<polarssl_cryptogram> cgs);

//Is the cryptogram generated in this run?
fixpoint bool polarssl_cryptogram_is_generated(polarssl_cryptogram cg);

//How deep are cryptograms nested through their payload?
fixpoint nat polarssl_cryptogram_level(polarssl_cryptogram cg);

//Upper bound on the nesting of cryptograms.
fixpoint nat polarssl_cryprogram_level_bound();

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL character representation of cryptograms ///////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

lemma void polarssl_chars_for_cryptogram_injective(polarssl_cryptogram cg1,
                                                   polarssl_cryptogram cg2);
  requires polarssl_cryptogram_tag(cg1) == polarssl_cryptogram_tag(cg2) &*&
           polarssl_chars_for_cryptogram(cg1) ==
           polarssl_chars_for_cryptogram(cg2);
  ensures  collision_in_run() ? true : (cg1 == cg2);

lemma polarssl_cryptogram
               polarssl_chars_for_cryptogram_surjective(list<char> cs, int tag);
  requires 1 <= tag &*& tag <= 10;
  ensures  polarssl_cryptogram_tag(result) == tag &*&
           cs == polarssl_chars_for_cryptogram(result);

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL upper bound on cryptograms exposed by a list of characters ////////
///////////////////////////////////////////////////////////////////////////////

/*@

lemma void polarssl_cryptograms_in_chars_bound_from(
                                                 list<char> cs, 
                                                 list<polarssl_cryptogram> cgs);
  requires true == polarssl_cryptograms_in_chars_bound(cs, cgs);
  ensures  true == subset(polarssl_cryptograms_in_chars(cs), cgs);

lemma void polarssl_cryptograms_in_chars_bound_to(list<char> cs);
  requires true;
  ensures  true == polarssl_cryptograms_in_chars_bound(
                                         cs, polarssl_cryptograms_in_chars(cs));

lemma void polarssl_cryptograms_in_chars_bound_join(
                                list<char> cs1, list<polarssl_cryptogram> cgs1,
                                list<char> cs2, list<polarssl_cryptogram> cgs2);
  requires polarssl_cryptograms_in_chars_bound(cs1, cgs1) &&
           polarssl_cryptograms_in_chars_bound(cs2, cgs2);
  ensures  true == polarssl_cryptograms_in_chars_bound(
                                           append(cs1, cs2), union(cgs1, cgs2));

lemma void polarssl_cryptograms_in_chars_bound_split(
                           list<char> cs, list<polarssl_cryptogram> cgs, int i);
  requires 0 <= i && i <= length(cs) &&
           polarssl_cryptograms_in_chars_bound(cs, cgs);
  ensures  polarssl_cryptograms_in_chars_bound(take(i, cs), cgs) &&
           polarssl_cryptograms_in_chars_bound(drop(i, cs), cgs);

lemma void polarssl_cryptograms_in_chars_bound_subset(
                                                list<char> cs, 
                                                list<polarssl_cryptogram> cgs1,
                                                list<polarssl_cryptogram> cgs2);
  requires subset(cgs1, cgs2) && 
           polarssl_cryptograms_in_chars_bound(cs, cgs1);
  ensures  true == polarssl_cryptograms_in_chars_bound(cs, cgs2);

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL generated cryptograms /////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

lemma void polarssl_cryptogram_constraints(list<char> cs,
                                           polarssl_cryptogram cg);
     requires cs == polarssl_chars_for_cryptogram(cg);
     ensures  cons(cg, nil) == polarssl_cryptograms_in_chars(cs);

predicate polarssl_cryptogram(char* chars, int len, list<char> cs,
                              polarssl_cryptogram cg) =
  chars(chars, len, cs) &*&
  cs == polarssl_chars_for_cryptogram(cg) &&
  true == polarssl_cryptogram_is_generated(cg) &&
  //Not necessary but for convenience
  cons(cg, nil) == polarssl_cryptograms_in_chars(cs) &&
  true == polarssl_cryptograms_in_chars_bound(cs, cons(cg, nil))
;

//Derived
lemma void polarssl_cryptogram_in_bound(list<char> cs, polarssl_cryptogram cg,
                                        list<polarssl_cryptogram> cgs);
  requires cs == polarssl_chars_for_cryptogram(cg) &&
           true == polarssl_cryptograms_in_chars_bound(cs, cgs);
  ensures  true == mem(cg, cgs);

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL public characters /////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate_ctor polarssl_public_generated_chars
                               (predicate(polarssl_cryptogram) polarssl_pub)
                               (list<char> cs) =
  [_]dummy_foreach(polarssl_cryptograms_in_chars(cs), polarssl_pub) &*&
  true == forall(polarssl_cryptograms_in_chars(cs),
                 polarssl_cryptogram_is_generated)
;

lemma void polarssl_public_generated_chars_assume(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    list<char> cs);
  requires true;
  ensures  [_]polarssl_public_generated_chars(polarssl_pub)(cs);

//Derived
lemma void polarssl_public_generated_cryptogram_chars(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    polarssl_cryptogram cg);
  requires true == polarssl_cryptogram_is_generated(cg) &*& [_]polarssl_pub(cg);
  ensures  [_]polarssl_public_generated_chars(polarssl_pub)(
                                             polarssl_chars_for_cryptogram(cg));

//Derived
lemma void polarssl_public_generated_chars_extract(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    list<char> cs, polarssl_cryptogram cg);
  requires [_]polarssl_public_generated_chars(polarssl_pub)(cs) &*&
           true == mem(cg, polarssl_cryptograms_in_chars(cs)) ||
           cs == polarssl_chars_for_cryptogram(cg);
  ensures  true == polarssl_cryptogram_is_generated(cg) &*& [_]polarssl_pub(cg);

//Derived
lemma void polarssl_public_generated_chars_join(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs1, list<char> cs2);
  requires [_]polarssl_public_generated_chars(polarssl_pub)(cs1) &*&
           [_]polarssl_public_generated_chars(polarssl_pub)(cs2);
  ensures  [_]polarssl_public_generated_chars(polarssl_pub)(append(cs1, cs2));

//Derived
lemma void polarssl_public_generated_chars_split(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs, int i);
     requires 0 <= i && i <= length(cs) &*&
              [_]polarssl_public_generated_chars(polarssl_pub)(cs);
     ensures  [_]polarssl_public_generated_chars(polarssl_pub)(take(i, cs)) &*&
              [_]polarssl_public_generated_chars(polarssl_pub)(drop(i, cs));

///////////////////////////////////////////////////////////////////////////////
// PolarSSL public messages ///////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate_ctor polarssl_public_message
         (predicate(polarssl_cryptogram) polarssl_pub)
         (char* chars, int len, list<char> cs) =
  chars(chars, len, cs) &*&
  [_]polarssl_public_generated_chars(polarssl_pub)(cs)
;

//Derived
lemma void polarssl_public_message_from_cryptogram(
                   predicate(polarssl_cryptogram) polarssl_pub,
                   char* chars, int len, list<char> cs, polarssl_cryptogram cg);
  requires polarssl_cryptogram(chars, len, cs, cg) &*&
           [_]polarssl_pub(cg);
  ensures  polarssl_public_message(polarssl_pub)(chars, len, cs);

@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL level of generated cryptograms ////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

fixpoint bool polarssl_cryprogram_has_lower_level(nat bound, 
                                                  polarssl_cryptogram cg)
{
  return int_of_nat(polarssl_cryptogram_level(cg)) < int_of_nat(bound);
}

lemma void polarssl_cryprogram_level_bound_apply(polarssl_cryptogram cg);
  requires true == polarssl_cryptogram_is_generated(cg);
  ensures  true == polarssl_cryprogram_has_lower_level(
                            succ(polarssl_cryprogram_level_bound()), cg);

lemma void polarssl_cryptogram_level_flat_constraints(polarssl_cryptogram cg);
  requires true == polarssl_cryptogram_is_generated(cg);
  ensures  polarssl_cryptogram_is_nested(cg) ?
             polarssl_cryptogram_level(cg) != zero
           :
             polarssl_cryptogram_level(cg) == zero;

lemma void polarssl_cryptogram_level_nested_constraints(
                           polarssl_cryptogram cg1, polarssl_cryptogram cg2);
  requires polarssl_cryptogram_is_generated(cg1) &&
           polarssl_cryptogram_is_nested(cg1) &&
           mem(cg2, polarssl_cryptograms_in_chars(
                                             polarssl_cryptogram_payload(cg1)));
  ensures  true == polarssl_cryprogram_has_lower_level(
                                           polarssl_cryptogram_level(cg1), cg2);

//Derived
lemma void polarssl_cryptogram_level_nested_constraints_bound(
                                       polarssl_cryptogram cg, nat bound);
  requires polarssl_cryptogram_is_generated(cg) &&
           polarssl_cryptogram_is_nested(cg) &&
           polarssl_cryprogram_has_lower_level(succ(bound), cg);
  ensures  true == forall(
                 polarssl_cryptograms_in_chars(polarssl_cryptogram_payload(cg)),
                            (polarssl_cryprogram_has_lower_level)(bound));

//Derived
lemma void polarssl_cryptograms_generated_level_bound(
                                                 list<polarssl_cryptogram> cgs);
  requires true == forall(cgs, polarssl_cryptogram_is_generated);
  ensures  true == forall(cgs, (polarssl_cryprogram_has_lower_level)
                               (succ(polarssl_cryprogram_level_bound())));
@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL random cryptogram - see "havege.h" ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct havege_state
{
  char content[POLARSSL_CHAR_SIZE_OF_HAVEGE_STATE];
};
typedef struct havege_state havege_state;

/*@

predicate havege_state(havege_state *state) =
  chars((void*) state, POLARSSL_CHAR_SIZE_OF_HAVEGE_STATE, _) &*&
  struct_havege_state_padding(state)
;

predicate havege_state_initialized(havege_state *state);

predicate random_request(int principal, int info, bool key) = true;

@*/

void havege_init(havege_state *havege_state);
  /*@ requires havege_state(havege_state); @*/
  /*@ ensures  havege_state_initialized(havege_state); @*/

void havege_free(havege_state *havege_state);
  //@ requires havege_state_initialized(havege_state);
  //@ ensures  havege_state(havege_state);

int havege_random(void *havege_state, char *output, size_t len);
  /*@ requires [?f]havege_state_initialized(havege_state) &*&
               random_request(?principal, ?info, ?key_request) &*&
               polarssl_generated_values(principal, ?count) &*&
               chars(output, len, _) &*& len >= POLARSSL_MIN_RANDOM_BYTE_SIZE;
  @*/
  /*@ ensures  [f]havege_state_initialized(havege_state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               result == 0 ?
                 polarssl_cryptogram(output, len, ?cs, ?cg) &*&
                 info == polarssl_cryptogram_info(cg) &*&
                 key_request ?
                   cg == polarssl_symmetric_key(principal, count + 1)
                 :
                   cg == polarssl_random(principal, count + 1)
               :
                 chars(output, len, _);
  @*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL hmac cryptogram - see "sha512.h" //////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sha512(const char *input, size_t ilen, char* output, int is384);
  /*@ requires [?f1]chars(input, ilen, ?cs_pay) &*&
                 ilen >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
               chars(output, 64, _) &*& (is384 == 0 || is384 == 1); @*/
  /*@ ensures  [f1]chars(input, ilen, cs_pay) &*&
               polarssl_cryptogram(output, ?length, ?cs, ?cg) &*&
               cg == polarssl_hash(cs_pay) &*&
               is384 == 0 ?
                 length == 64
               :
                 length == 48 &*& chars(output + 48, 16, _);  @*/

void sha512_hmac(const char *key, size_t keylen, const char *input, size_t ilen,
                 char *output, int is384);
  /*@ requires [?f0]polarssl_world(?polarssl_pub) &*&
               [?f1]chars(key, keylen, ?cs_key) &*&
                 polarssl_key_id(?p, ?c) &*&
               [?f2]chars(input, ilen, ?cs_pay) &*&
                 ilen >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
               chars(output, ?length, _) &*&
               is384 == 0 ? 
                   length == 64
                 :
                   length == 48 && is384 == 1; @*/
  /*@ ensures  [f0]polarssl_world(polarssl_pub) &*&
               [f1]chars(key, keylen, cs_key) &*& 
               [f2]chars(input, ilen, cs_pay) &*&
               cs_key == polarssl_chars_for_cryptogram(
                           polarssl_symmetric_key(p, c)) ?
                 polarssl_cryptogram(output, length, ?cs, ?cg) &*&
                 cg == polarssl_hmac(p, c, cs_pay)
               :
                 polarssl_public_message(polarssl_pub)(output, length, _); @*/
                 

///////////////////////////////////////////////////////////////////////////////
// Polarssl symmetric encrypted cryptogram - see "aes.h" //////////////////////
///////////////////////////////////////////////////////////////////////////////

struct aes_context
{
  char content[POLARSSL_CHAR_SIZE_OF_AES_CONTEXT];
};
typedef struct aes_context aes_context;

/*@

predicate aes_context(aes_context *context) =
  chars((void*) context, POLARSSL_CHAR_SIZE_OF_AES_CONTEXT, _) &*&
  struct_aes_context_padding(context)
;
predicate aes_context_initialized(aes_context *context, 
                                  option<pair<int, int> > key_id);

@*/

int aes_setkey_enc(aes_context *ctx, const char *key, unsigned int keysize);
  /*@ requires [?f]chars(key, ?size_key, ?cs_key) &*& 
                 keysize == size_key * 8 &*&
                 polarssl_key_id(?p, ?c) &*&
               aes_context(ctx) &*&
               (keysize == 128 || keysize == 192 || keysize == 256); @*/
  /*@ ensures  [f]chars(key, size_key, cs_key) &*&
               result == 0 ?
                 aes_context_initialized(ctx, ?key_id) &*&
                 (
                   cs_key == polarssl_chars_for_cryptogram(
                               polarssl_symmetric_key(p, c)) ?
                     key_id == some(pair(p, c))
                   :
                     key_id == none
                 )
               :
                 aes_context(ctx); @*/

void aes_free(aes_context *ctx);
  //@ requires aes_context_initialized(ctx, ?key_id);
  //@ ensures  aes_context(ctx);

int aes_crypt_cfb128(aes_context *ctx, int mode, size_t length, 
                                size_t *iv_off, char *iv, 
                                const char *input, char *output);
  /*@ requires
        [?f0]polarssl_world(?polarssl_pub) &*&
        aes_context_initialized(ctx, ?key_id) &*&
        (mode == POLARSSL_AES_ENCRYPT || mode == POLARSSL_AES_DECRYPT) &*&
        chars(iv, 16, ?cs_iv) &*& u_integer(iv_off, ?iv_off_val) &*&
        iv_off_val >= 0 &*& iv_off_val < 16 &*&
        [?f1]chars(input, length, ?cs_input) &*&
          length >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
        chars(output, length, _); @*/
  /*@ ensures
        [f0]polarssl_world(polarssl_pub) &*&
        aes_context_initialized(ctx, key_id) &*&
        chars(iv, 16, _) &*& u_integer(iv_off, _) &*&
        [f1]chars(input, length, cs_input) &*&
        result == 0 ?
          mode == POLARSSL_AES_ENCRYPT ?
          (
            switch(key_id)
            {
              case some(pair) : return
                switch (pair)
                { 
                  case pair(principal, id): return
                    polarssl_cryptogram(output, length, ?cs, ?cg) &*&
                    true == polarssl_cryptogram_is_generated(cg) &*&
                    cg == polarssl_encrypted(
                                      principal, id, cs_input, 
                                      append(chars_of_int(iv_off_val), cs_iv));
                };
              case none: return
                polarssl_public_message(polarssl_pub)(output, length, _);
            }
          ) :
          mode == POLARSSL_AES_DECRYPT ?
          (
            switch(key_id)
            {
              case some(pair) : return
                switch (pair)
                { 
                  case pair(principal, id): return
                    chars(output, length, ?cs_output) &*&
                    cs_input == polarssl_chars_for_cryptogram(
                                  polarssl_encrypted(
                                      principal, id, cs_output,
                                      append(chars_of_int(iv_off_val), cs_iv)));
                };
              case none: return
                polarssl_public_message(polarssl_pub)(output, length, _);
            }
          ) :
          false
        :
          chars(output, length, _); @*/

///////////////////////////////////////////////////////////////////////////////
// Polarssl authenticated encrypted cryptogram - see "gcm.h" //////////////////
///////////////////////////////////////////////////////////////////////////////

struct gcm_context
{
  char content[POLARSSL_CHAR_SIZE_OF_GCM_CONTEXT];
};
typedef struct gcm_context gcm_context;

/*@

predicate gcm_context(gcm_context *context) =
  chars((void*) context, POLARSSL_CHAR_SIZE_OF_GCM_CONTEXT, _) &*&
  struct_gcm_context_padding(context)
;
predicate gcm_context_initialized(gcm_context *context, 
                                  option<pair<int, int> > key_id);

@*/

int gcm_init(gcm_context *ctx, int cipher, 
             const char *key, unsigned int keysize);
  /*@ requires [?f]chars(key, ?size_key, ?cs_key) &*&
                 keysize == size_key * 8 &*&
                 polarssl_key_id(?p, ?c) &*&
               gcm_context(ctx) &*& 
               (keysize == 128 || keysize == 192 || keysize == 256) &*&
               // only AES supported for now
               cipher == POLARSSL_AES_CIPHER_ID; @*/
  /*@ ensures  [f]chars(key, size_key / 8, cs_key) &*&
               result == 0 ?
                 gcm_context_initialized(ctx, ?key_id) &*&
                 (
                   cs_key == polarssl_chars_for_cryptogram(
                               polarssl_symmetric_key(p, c)) ?
                     key_id == some(pair(p, c))
                   :
                     key_id == none
                 )
               :
                 gcm_context(ctx); @*/

void gcm_free(gcm_context *ctx);
  //@ requires gcm_context_initialized(ctx, ?key_id);
  //@ ensures  gcm_context(ctx);

int gcm_crypt_and_tag(gcm_context *ctx, int mode, size_t length,
                      const char *iv, size_t iv_len, 
                      const char *add, size_t add_len,
                      const char *input, char *output, 
                      size_t tag_len, char *tag);
  /*@ requires
        [?f0]polarssl_world(?polarssl_pub) &*&
        gcm_context_initialized(ctx, ?key_id) &*&
        // this function is only spec'ed for encryption, use the function 
        // gcm_auth_decrypt to decrypt
        (mode == POLARSSL_GCM_ENCRYPT) &*&
        // iv_len must be 16 since only AES is supported
          chars(iv, iv_len, ?cs_iv) &*& iv_len == 16 &*&
        // no additional data supported yet
          add == NULL &*& add_len == 0 &*&
        [?f1]chars(input, length, ?cs_in) &*&
          length >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
        chars(tag, 16, ?tag_cs_in) &*& 
        chars(output, length, _); @*/
  /*@ ensures
        [f0]polarssl_world(polarssl_pub) &*&
        gcm_context_initialized(ctx, key_id) &*&
        chars(iv, 16, _) &*&
        [f1]chars(input, length, cs_in) &*&
        result == 0 ?
          chars(tag, tag_len, ?tag_cs_out) &*&
          switch(key_id)
          {
            case some(pair) : return
              switch (pair)
              { 
                case pair(principal, id): return
                  polarssl_cryptogram(output, length, ?cs_out, ?cg_out) &*&
                  cg_out == polarssl_auth_encrypted(
                              principal, id, tag_cs_out, cs_in, cs_iv);
              };
            case none: return
              polarssl_public_message(polarssl_pub)(output, length, _);
          }
        :
          chars(tag, tag_len, _) &*&
          chars(output, length, _); @*/

int gcm_auth_decrypt(gcm_context *ctx, size_t length,
                     const char *iv, size_t iv_len,
                     const char *add, size_t add_len,
                     const char *tag, size_t tag_len,
                     const char *input, char *output);
  /*@ requires
        gcm_context_initialized(ctx, ?key_id) &*&
        // iv_len must be 16 since only AES is supported
          chars(iv, iv_len, ?cs_iv) &*& iv_len == 16 &*&
        // no additional data supported yet
          add == NULL &*& add_len == 0 &*&
        [?f]chars(input, length, ?cs_in) &*&
          length >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
        chars(tag, 16, ?tag_cs_in) &*& 
        chars(output, length, _); @*/
  /*@ ensures
        gcm_context_initialized(ctx, key_id) &*&
        chars(iv, 16, _) &*&
        [f]chars(input, length, cs_in) &*&
        chars(tag, tag_len, _) &*&
        result == 0 ?
          switch(key_id)
          {
            case some(pair) : return
              switch (pair)
              { 
                case pair(principal, id): return
                  chars(output, length, ?cs_out) &*&
                  cs_in == polarssl_chars_for_cryptogram(
                    polarssl_auth_encrypted(
                      principal, id, tag_cs_in, cs_out, cs_iv));
              };
            case none: 
              return false;
          }
        :
          chars(output, length, _); @*/

///////////////////////////////////////////////////////////////////////////////
// Polarssl asymetric encrypted cryptogram - see "pk.h" and "rsa.h" ///////////
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
                              int bit_size, option<pair<int, int> > id);

predicate pk_context_with_keys(pk_context *context, int principal,
                               int count, int bit_size, int info);

predicate pk_context_garbage(pk_context *context);

predicate rsa_key_request(int principal, int info) = emp;
@*/

void pk_init(pk_context *ctx);
  //@ requires pk_context(ctx);
  //@ ensures  pk_context_initialized(ctx);

const pk_info_t *pk_info_from_type(int pk_type);
  //@ requires pk_type == POLARSSL_PK_RSA_TYPE;
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
  requires pk_context_with_key(ctx, _, _, _);
  ensures  pk_context_garbage(ctx);

lemma void pk_release_context_with_keys(pk_context *ctx);
  requires pk_context_with_keys(ctx, _, _, _, _);
  ensures  pk_context_garbage(ctx);
@*/

void pk_free(pk_context *ctx);
/*@ requires pk_context_garbage(ctx); @*/
/*@ ensures  pk_context(ctx);  @*/

typedef int random_function/*@(predicate(void *) state_pred)@*/
                              (void* state, char* buff, size_t len);
  /*@ requires [?f]state_pred(state) &*&
               random_request(?principal, ?info, ?key_request) &*&
               polarssl_generated_values(principal, ?count) &*&
               chars(buff, len, _) &*& len >= POLARSSL_MIN_RANDOM_BYTE_SIZE; @*/
  /*@ ensures  [f]state_pred(state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               result == 0 ?
                 polarssl_cryptogram(buff, len, ?cs, ?cg) &*&
                 info == polarssl_cryptogram_info(cg) &*&
                 key_request ?
                   cg == polarssl_symmetric_key(principal, count + 1)
                 :
                   cg == polarssl_random(principal, count + 1)
               :
                 chars(buff, len, _); @*/

//@ predicate random_function_predicate(predicate(void *) state_pred) = true;

int rsa_gen_key(void *ctx, void *f_rng, void *p_rng,
                unsigned int nbits, int exponent);
  /*@ requires random_function_predicate(?state_pred) &*&
               pk_context_initialized2(?pk_context, ctx) &*&
               pk_context->pk_ctx |-> ctx &*&
               rsa_key_request(?principal, ?info) &*&
               [_]is_random_function(f_rng, state_pred) &*&
               [?f]state_pred(p_rng) &*&
               nbits >= 1024 && nbits <= 8192 &*& exponent == 65537 &*&
               polarssl_generated_values(principal, ?count); @*/
  /*@ ensures  [f]state_pred(p_rng) &*&
               polarssl_generated_values(principal, count + 1) &*&
               pk_context_with_keys(pk_context, principal, 
                                    count + 1, nbits, info); @*/

int pk_write_pubkey_pem(pk_context *ctx, char *buf, size_t size);
  /*@ requires pk_context_with_keys(ctx, ?principal, ?count, ?nbits, ?info) &*&
               //To fix size and to ensure that there is enough space.
               chars(buf, size, _) &*& nbits == size; @*/ 
  /*@ ensures  pk_context_with_keys(ctx, principal, count, nbits, info) &*&
               result == 0 ?
                 polarssl_cryptogram(buf, size, ?key_cs, ?key) &*&
                 key == polarssl_public_key(principal, count) &*&
                 info == polarssl_cryptogram_info(key)
               :
                 chars(buf, size, _); 
  @*/

int pk_write_key_pem(pk_context *ctx, char *buf, size_t size);
  /*@ requires pk_context_with_keys(ctx, ?principal, ?count, ?nbits, ?info) &*&
               //To fix size and to ensure that there is enough space.
               chars(buf, size, _) &*&  nbits == size; @*/
  /*@ ensures  pk_context_with_keys(ctx, principal, count, nbits, info) &*&
               result == 0 ?
                 polarssl_cryptogram(buf, size, ?key_cs, ?key) &*&
                 key == polarssl_private_key(principal, count) &*&
                 info == polarssl_cryptogram_info(key)
               :
                 chars(buf, size, _); 
  @*/

/*@
lemma void polarssl_info_for_keypair(int principal, int count);
  requires true;
  ensures  polarssl_cryptogram_info(polarssl_public_key(principal, count)) ==
           polarssl_cryptogram_info(polarssl_private_key(principal, count));
@*/

int pk_parse_public_key(pk_context *ctx, const char *key, size_t keylen);
  /*@ requires pk_context_initialized(ctx) &*&
               [?f]chars(key, keylen, ?cs_key) &*&
                 polarssl_key_id(?p, ?c); @*/
  /*@ ensures  [f]chars(key, keylen, cs_key) &*& 
               result == 0 ?
                 pk_context_with_key(ctx, pk_public, keylen, ?key_id) &*&
                 (
                   cs_key == polarssl_chars_for_cryptogram(
                               polarssl_public_key(p, c)) ?
                     key_id == some(pair(p, c))
                   :
                     key_id == none
                 )
               :
                 pk_context_garbage(ctx); @*/

int pk_parse_key(pk_context *ctx, const char *key, size_t keylen,
                                  const char *pwd, size_t pwdlen);
  /*@ requires pk_context_initialized(ctx) &*&
               pwd == NULL &*& pwdlen == 0 &*&
               [?f]chars(key, keylen, ?cs_key) &*& 
                 polarssl_key_id(?p, ?c); @*/
  /*@ ensures  [f]chars(key, keylen, cs_key) &*& 
               result == 0 ?
                 pk_context_with_key(ctx, pk_private, keylen, ?key_id) &*&
                 (
                   cs_key == polarssl_chars_for_cryptogram(
                               polarssl_private_key(p, c)) ?
                     key_id == some(pair(p, c))
                   :
                     key_id == none
                 )
               :
                 pk_context_garbage(ctx); @*/
  
int pk_encrypt(pk_context *ctx, const char *input, size_t ilen, char *output, 
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  [?f0]polarssl_world(?polarssl_pub) &*&
                random_function_predicate(?state_pred) &*&
                pk_context_with_key(ctx, pk_public, ?nbits, ?key_id) &*&
                [?f1]chars(input, ilen, ?cs_in) &*&
                  ilen >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
                  // encrypted message can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                polarssl_generated_values(?principal, ?count); @*/
  /*@ ensures   [f0]polarssl_world(polarssl_pub) &*&
                pk_context_with_key(ctx, pk_public, nbits, key_id) &*&
                [f1]chars(input, ilen, cs_in) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                polarssl_generated_values(principal, count + 1) &*&
                result == 0 ?
                  olen_val > 0 &*& olen_val < osize &*& 
                  8 * olen_val <= nbits &*&
                  chars(output + olen_val, osize - olen_val, _) &*&
                  switch(key_id)
                  {
                    case some(pair) : return
                      switch (pair)
                      { 
                        case pair(principal1, id1): return
                          polarssl_cryptogram(output, olen_val, 
                                              ?cs_out, ?cg_out) &*&
                          cg_out == polarssl_asym_encrypted(
                                                  principal1, id1, cs_in, ?ent);
                      };
                    case none: return
                      polarssl_public_message(polarssl_pub)
                                             (output, olen_val, _);
                  }
                :
                  chars(output, osize, _)
                ; @*/

int pk_decrypt(pk_context *ctx, const char *input, size_t ilen, char *output, 
               size_t *olen, size_t osize, void *f_rng, void *p_rng);
  /*@ requires  [?f0]polarssl_world(?polarssl_pub) &*&
                random_function_predicate(?state_pred) &*&
                pk_context_with_key(ctx, pk_private, ?nbits, ?key_id) &*&
                [?f1]chars(input, ilen, ?cs_in) &*&
                  ilen >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
                  // message to decrypt can not be bigger than key
                  ilen * 8 <= nbits &*&
                u_integer(olen, _) &*&
                chars(output, osize, _) &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                polarssl_generated_values(?principal1, ?count1); @*/
  /*@ ensures   [f0]polarssl_world(polarssl_pub) &*&
                pk_context_with_key(ctx, pk_private, nbits, key_id) &*&
                [f1]chars(input, ilen, cs_in) &*&
                u_integer(olen, ?olen_val) &*&
                [f2]state_pred(p_rng) &*&
                polarssl_generated_values(principal1, count1 + 1) &*&
                result == 0 ?
                  olen_val * 2 > ilen &*&
                  chars(output + olen_val, osize - olen_val, _) &*&
                  exists<polarssl_cryptogram>(?cg_in) &*&
                  cs_in == polarssl_chars_for_cryptogram(cg_in) &*&
                  cg_in == polarssl_asym_encrypted(?principal2, ?id2, 
                                                   ?cs_out2, ?ent2) &*&
                  switch(key_id)
                  {
                    case some(pair) : return
                      switch (pair)
                      { 
                        case pair(principal3, id3): return
                          principal2 == principal3 && id2 == id3 ?
                            chars(output, olen_val, cs_out2)
                          :
                            polarssl_public_message(polarssl_pub)
                                                   (output, olen_val, _);
                      };
                    case none: return
                      polarssl_public_message(polarssl_pub)
                                             (output, olen_val, _);
                  }
                :
                  chars(output, osize, _)
                ; @*/

int pk_sign(pk_context *ctx, int md_alg, const char *hash, size_t hash_len,
            char *sig, size_t *sig_len, void *f_rng, void *p_rng);
  /*@ requires  [?f0]polarssl_world(?polarssl_pub) &*&
                random_function_predicate(?state_pred) &*&
                pk_context_with_key(ctx, pk_private, ?nbits, ?key_id) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f1]chars(hash, hash_len, ?cs_in) &*&
                  hash_len >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
                  // hash to sign can not be bigger than key
                  hash_len * 8 <= nbits &*&
                u_integer(sig_len, _) &*&
                chars(sig, ?out_len, _) &*& 8 * out_len >= nbits &*&
                [_]is_random_function(f_rng, state_pred) &*&
                [?f2]state_pred(p_rng) &*&
                polarssl_generated_values(?principal1, ?count1); @*/
  /*@ ensures   [f0]polarssl_world(polarssl_pub) &*&
                pk_context_with_key(ctx, pk_private, nbits, key_id) &*&
                [f1]chars(hash, hash_len, cs_in) &*&
                u_integer(sig_len, ?sig_len_val) &*&
                [f2]state_pred(p_rng) &*&
                polarssl_generated_values(principal1, count1 + 1) &*&
                result == 0 ?
                  sig_len_val > 0 &*& sig_len_val <= out_len &*& 
                  chars(sig + sig_len_val, out_len - sig_len_val, _) &*&
                  switch(key_id)
                  {
                    case some(pair) : return
                      switch (pair)
                      { 
                        case pair(principal2, count2): return
                          polarssl_cryptogram(sig, sig_len_val, 
                                              ?cs_out, ?cg_out) &*&
                          cg_out == polarssl_asym_signature(
                                               principal2, count2, cs_in, ?ent);
                      };
                    case none: return
                      polarssl_public_message(polarssl_pub)(sig, sig_len_val, _);
                  }
                :
                  chars(sig, out_len, _); @*/

int pk_verify(pk_context *ctx, int md_alg, const char *hash, 
              size_t hash_len, const char *sig, size_t sig_len );
  /*@ requires  pk_context_with_key(ctx, pk_public, ?nbits, ?key_id) &*&
                // only signing of a general buffer for now
                md_alg == POLARSSL_MD_NONE &*&
                [?f0]chars(hash, hash_len, ?cs_in) &*&
                  hash_len >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
                  // hash to verify can not be bigger than key
                  hash_len * 8 <= nbits &*&
                [?f1]chars(sig, sig_len, ?cs_sig); @*/
  /*@ ensures   pk_context_with_key(ctx, pk_public, nbits, key_id) &*&
                [f0]chars(hash, hash_len, cs_in) &*&
                [f1]chars(sig, sig_len, cs_sig) &*&
                result == 0 ?
                  switch(key_id)
                  {
                    case some(pair) : return
                      switch (pair)
                      { 
                        case pair(principal2, id2): return
                          exists<list<char> >(?ent) &*&
                          cs_sig == polarssl_chars_for_cryptogram(
                                      polarssl_asym_signature(
                                        principal2, id2, cs_in, ent));
                      };
                    case none: return
                      false;
                  }
                :
                  true
                ; @*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL networking - see "net.h" //////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

inductive socket_status =
 | bound_to_port
 | connection_init
 | connected
;

predicate polarssl_net_status(int socket, list<char> socket_ip, 
                              int socket_port, socket_status socket_stat);
@*/

int net_connect(int *fd, const char *host, int port);
  //@ requires integer(fd, _) &*& [?f]option_string(host, ?s_ip);
  /*@ ensures  integer(fd, ?s_fd) &*& [f]option_string(host, s_ip) &*&
               result == 0 ?
                   polarssl_net_status(s_fd, s_ip, port, connection_init) 
                 :
                   true; @*/

int net_set_block(int fd);
  //@ requires polarssl_net_status(fd, ?s_ip, ?port, connection_init);
  /*@ ensures  result == 0 ?
                   polarssl_net_status(fd, s_ip, port, connected) 
                 :
                   true; @*/

int net_bind(int *fd, const char *bind_ip, int port);
  //@ requires integer(fd, _) &*& [?f]option_string(bind_ip, ?s_ip);
  /*@ ensures  integer(fd, ?s_fd) &*& [f]option_string(bind_ip, s_ip) &*&
               result == 0 ?
                   polarssl_net_status(s_fd, s_ip, port, bound_to_port)
                 :
                   true; @*/

int net_accept(int bind_fd, int *client_fd, void *client_ip);
  /*@ requires integer(client_fd, _) &*& option_string(client_ip, ?c_ip) &*&
               polarssl_net_status(bind_fd, ?ip, ?port, bound_to_port); @*/
  /*@ ensures  integer(client_fd, ?c_fd) &*& option_string(client_ip, c_ip) &*& 
               polarssl_net_status(bind_fd, ip, port, bound_to_port) &*&
               result == 0 ?
                   polarssl_net_status(c_fd, c_ip, _, connection_init)
                 :
                   true; @*/
  
void net_usleep(unsigned long usec);
  //@ requires true;
  //@ ensures  true;

int net_send(void *ctx, const char *buf, size_t len);
  /*@ requires [?f0]polarssl_world(?polarssl_pub) &*&
               integer(ctx, ?fd) &*&
               polarssl_net_status(fd, ?ip, ?port, connected) &*&
               len <= POLARSSL_MAX_MESSAGE_BYTE_SIZE &*&
               [?f1]polarssl_public_message(polarssl_pub)(buf, len, ?cs); @*/
  /*@ ensures  [f0]polarssl_world(polarssl_pub) &*&
               integer(ctx, fd)  &*&
               polarssl_net_status(fd, ip, port, connected) &*&
               [f1]polarssl_public_message(polarssl_pub)(buf, len, cs); @*/
  
int net_recv(void *ctx, char *buf, size_t len);
  /*@ requires [?f]polarssl_world(?polarssl_pub) &*&
               integer(ctx, ?fd)  &*&
               polarssl_net_status(fd, ?ip, ?port, connected) &*&
               chars(buf, len, _) &*& 
                 len <= POLARSSL_MAX_MESSAGE_BYTE_SIZE; @*/
  /*@ ensures  [f]polarssl_world(polarssl_pub) &*&
               integer(ctx, fd)  &*&
               polarssl_net_status(fd, ip, port, connected) &*&
               result <= 0 ?
                 chars(buf, len, _)
               :
                 (
                   result <= len &*& 
                   polarssl_public_message(polarssl_pub)(buf, result, _) &*&
                   chars(buf + result, len - result, _)
                 ); @*/

void net_close(int fd);
  //@ requires polarssl_net_status(fd, _, _, _);
  //@ ensures  true;

///////////////////////////////////////////////////////////////////////////////
// PolarSSL proof obligations /////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

typedef lemma void polarssl_bad_random_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram random);
  requires  polarssl_proof_pred() &*&
            random == polarssl_random(?p, _) &*&
            true == bad(p);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(random);

typedef lemma void polarssl_bad_key_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key);
  requires  polarssl_proof_pred() &*&
            key == polarssl_symmetric_key(?p, _) &*&
            true == bad(p);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(key);

typedef lemma void polarssl_public_key_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key);
  requires  polarssl_proof_pred() &*&
            key == polarssl_public_key(_, _);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(key);
     
typedef lemma void polarssl_bad_private_key_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key);
  requires  polarssl_proof_pred() &*&
            key == polarssl_private_key(?p, _) &*&
            true == bad(p);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(key);
  
typedef lemma void polarssl_hash_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram hash);
  requires  polarssl_proof_pred() &*&
            hash == polarssl_hash(?pay) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(hash);

typedef lemma void polarssl_public_hmac_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram hmac);
  requires  polarssl_proof_pred() &*&
            hmac == polarssl_hmac(?p, ?c, ?pay) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_pub(polarssl_symmetric_key(p, c)) &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(hmac);

typedef lemma void polarssl_public_encryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            encrypted == polarssl_encrypted(?p, ?c, ?pay, ?ent) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_pub(polarssl_symmetric_key(p, c)) &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(encrypted);
 
typedef lemma void polarssl_public_decryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key, 
                          polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            key == polarssl_symmetric_key(?p, ?c) &*&
            encrypted == polarssl_encrypted(p, c, ?pay, ?ent) &*&
            [_]polarssl_pub(key) &*&
            [_]polarssl_pub(encrypted);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);

typedef lemma void polarssl_public_auth_encryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            encrypted == polarssl_auth_encrypted(?p, ?c, ?mac, ?pay, ?ent) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_pub(polarssl_symmetric_key(p, c)) &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(encrypted);

typedef lemma void polarssl_public_auth_decryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key, 
                          polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            key == polarssl_symmetric_key(?p, ?c) &*&
            encrypted == polarssl_auth_encrypted(p, c, ?mac, ?pay, ?ent) &*&
            [_]polarssl_pub(key) &*&
            [_]polarssl_pub(encrypted);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);

typedef lemma void polarssl_public_asym_encryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            encrypted == polarssl_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_pub(polarssl_public_key(p, c)) &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(encrypted);

typedef lemma void polarssl_public_asym_decryption_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram key, 
                          polarssl_cryptogram encrypted);
  requires  polarssl_proof_pred() &*&
            key == polarssl_private_key(?p, ?c) &*&
            encrypted == polarssl_asym_encrypted(p, c, ?pay, ?ent) &*&
            [_]polarssl_pub(key) &*& 
            [_]polarssl_pub(encrypted);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);

typedef lemma void polarssl_public_asym_signature_is_public(
                      predicate(polarssl_cryptogram) polarssl_pub,
                      predicate() polarssl_proof_pred)
                         (polarssl_cryptogram sig);
  requires  polarssl_proof_pred() &*&
            sig == 
              polarssl_asym_signature(?p, ?c, ?pay, ?ent) &*&
            length(pay) <= INT_MAX &*&
            [_]polarssl_pub(polarssl_private_key(p, c)) &*&
            [_]polarssl_public_generated_chars(polarssl_pub)(pay);
  ensures   polarssl_proof_pred() &*&
            [_]polarssl_pub(sig);

predicate polarssl_proof_obligations(
                     predicate(polarssl_cryptogram) pub,
                     predicate() pred) =
  is_polarssl_bad_random_is_public(_, pub, pred) &*&
  is_polarssl_bad_key_is_public(_, pub, pred) &*&
  is_polarssl_public_key_is_public(_, pub, pred) &*&
  is_polarssl_bad_private_key_is_public(_, pub, pred) &*&
  is_polarssl_hash_is_public(_, pub, pred) &*&
  is_polarssl_public_hmac_is_public(_, pub, pred) &*&
  is_polarssl_public_encryption_is_public(_, pub, pred) &*&
  is_polarssl_public_decryption_is_public(_, pub, pred) &*&
  is_polarssl_public_auth_encryption_is_public(_, pub, pred) &*&
  is_polarssl_public_auth_decryption_is_public(_, pub, pred) &*&
  is_polarssl_public_asym_encryption_is_public(_, pub, pred) &*&
  is_polarssl_public_asym_decryption_is_public(_, pub, pred) &*&
  is_polarssl_public_asym_signature_is_public(_, pub, pred)
;
@*/

///////////////////////////////////////////////////////////////////////////////
// PolarSSL attacker model ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void polarssl_attacker(int *i);
  /*@ requires [?f]polarssl_world(?polarssl_pub) &*&
               polarssl_proof_obligations(polarssl_pub, ?proof_pred) &*&
               proof_pred() &*&
               integer(i, ?count1) &*& count1 >= 0 &*&
               polarssl_principals(count1); @*/
  /*@ ensures  [f]polarssl_world(polarssl_pub) &*&
               polarssl_proof_obligations(polarssl_pub, proof_pred) &*&
               proof_pred() &*&
               integer(i, ?count2) &*& polarssl_principals(count2) &*&
               count2 > count1; @*/

#endif
