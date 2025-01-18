#ifndef SYMBOLIC_H
#define SYMBOLIC_H

#include <pthread.h>
#include <stdbool.h>
#include <string.h>

#include "../../annotated_api/mbedTLS_definitions.h"
//@ #include "proof_obligations.gh"

///////////////////////////////////////////////////////////////////////////////
// Module stuff ///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ require_module symbolic;

///////////////////////////////////////////////////////////////////////////////
// Principals /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
predicate principals_created(int p);

predicate world(predicate(item) pub, fixpoint(int, int, bool, bool) key_clsfy);
@*/

struct keypair;

int create_principal(struct keypair** keypair);
  /*@ requires world(?pub, ?key_clsfy) &*&
               *keypair |-> _ &*&
               principals_created(?count); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               principals_created(result) &*&
               result == count + 1 &*&
               principal(result, 1) &*&
               pointer(keypair, ?p_keypair) &*&
               keypair(p_keypair, result, 1, 0, pub); @*/

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib();
  /*@ requires module(symbolic, true) &*&
               is_key_classifier(_, ?pub, ?clsfy) &*&
               proof_obligations(pub); @*/
  //@ ensures  world(pub, clsfy) &*& principals_created(0);

void abort_crypto_lib(const char* message);
  //@ requires [?f]string(message, ?cs);
  //@ ensures  false;

void exit_crypto_lib();
  //@ requires world(?pub, ?key_clsfy) &*& principals_created(_);
  //@ ensures  true;

/*@

typedef lemma void not_public(predicate(item) pub, item i, int info)();
  requires  [_]pub(i);
  ensures   false;

@*/

///////////////////////////////////////////////////////////////////////////////
// Item ///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item;

/*@

inductive item =
  | data_item                 (list<char> data)
  | pair_item                 (item first, item second)
  | nonce_item                (int principal, int count, char inc)
  | symmetric_key_item        (int principal, int count)
  | public_key_item           (int principal, int count)
  | private_key_item          (int principal, int count)
  | hash_item                 (option<item> payload)
  | hmac_item                 (int principal, int count, option<item> payload)
  | symmetric_encrypted_item  (int principal, int count, option<item> payload,
                               list<crypto_char> entropy)
  | asymmetric_encrypted_item (int principal, int count, option<item> payload,
                               list<crypto_char> entropy)
  | asymmetric_signature_item (int principal, int count, option<item> payload,
                               list<crypto_char> entropy)
;

predicate item(struct item *item, item i, predicate(item) pub);

fixpoint int info_for_item(item i)
{
  switch(i)
  {
    case data_item(cs0):
      return 0;
    case pair_item(f0, s0):
      return 0;
    case nonce_item(p0, c0, inc0):
      return cg_info(cg_nonce(p0, c0));
    case hash_item(pay0):
      return 0;
    case symmetric_key_item(p0, c0):
      return cg_info(cg_symmetric_key(p0, c0));
    case public_key_item(p0, c0):
      return cg_info(cg_rsa_public_key(p0, c0));
    case private_key_item(p0, c0):
      return cg_info(cg_rsa_private_key(p0, c0));
    case hmac_item(p0, c0, pay0):
      return cg_info(cg_symmetric_key(p0, c0));
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      return cg_info(cg_symmetric_key(p0, c0));
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      return cg_info(cg_rsa_public_key(p0, c0));
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      return cg_info(cg_rsa_private_key(p0, c0));
  }
}

fixpoint bool well_formed_item(item i)
{
  switch (i)
  {
    case pair_item(f0, s0):
      return well_formed_item(f0) && well_formed_item(s0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(p):
          return well_formed_item(p);
        case none:
          return false;
      };
    case hmac_item(p0, c0, pay0): return
      switch (pay0)
      {
        case some(p):
          return well_formed_item(p);
        case none:
          return false;
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    default:
      return true;
  }
}

fixpoint bool none_payload_item(item i)
{
  switch (i)
  {
    case hash_item(pay0):                               return pay0 == none;
    case hmac_item(p0, c0, pay0):                       return pay0 == none;
    case symmetric_encrypted_item(p0, c0, pay0, ent0):  return pay0 == none;
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return pay0 == none;
    case asymmetric_signature_item(p0, c0, pay0, ent0): return pay0 == none;
    default:                                            return false;
  }
}

@*/

void item_free(struct item* item);
  //@ requires item(item, _, _);
  //@ ensures  emp;

struct item* item_clone(struct item* item);
  //@ requires [?f]item(item, ?i, ?pub);
  /*@ ensures  [f]item(item, i, pub) &*&
               item(result, i, pub) &*& result != 0; @*/

void item_check_equal(struct item* item1, struct item* item2);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [?f1]item(item1, ?i1, pub) &*& [?f2]item(item2, ?i2, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count) &*&
               [f1]item(item1, i1, pub) &*& [f2]item(item2, i2, pub) &*&
               col || i1 == i2; @*/

///////////////////////////////////////////////////////////////////////////////
// Data item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_data(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == data_item(_) : true; @*/

void check_is_data(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == data_item(_); @*/

struct item *create_data_item(char* data, int length);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               chars(data, length, ?cs) &*& length >= 4; @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               chars(data, length, cs) &*&
               item(result, data_item(cs), pub); @*/

struct item *create_data_item_from_int(int i);
  //@ requires [?f]world(?pub, ?key_clsfy);
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(result, data_item(chars_of_int(i)), pub); @*/

int item_get_data(struct item *item, char** data);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub) &*&
               i == data_item(?cs0) &*& pointer(data, _); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               pointer(data, ?p) &*&
               chars(p, result, ?cs1) &*& malloc_block(p, result) &*&
               col ? true : cs0 == cs1; @*/

//Only call this function if you expect the item was constructed with
// "create_data_item_from_char". If it receives a different item it will abort;
int item_get_data_as_int(struct item *item);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub) &*&
               i == data_item(?cs0); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               col ? true : result == int_of_chars(cs0); @*/

///////////////////////////////////////////////////////////////////////////////
// Pair item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_pair(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == pair_item(_, _) : true; @*/

void check_is_pair(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?p, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, p, pub) &*&
               p == pair_item(_, _); @*/

struct item *create_pair(struct item *first, struct item *second);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(first, ?f, pub) &*& [?f2]item(second, ?s, pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(first, f, pub) &*& [f2]item(second, s, pub) &*&
               item(result, pair_item(f, s), pub); @*/

struct item *pair_get_first(struct item *pair);
  //@ requires [?f0]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub, key_clsfy) &*& item(pair, p, pub) &*&
               p == pair_item(?fst, ?snd) &*&
               item(result, ?fst0, pub) &*&
               col ? true : fst == fst0; @*/

struct item *pair_get_second(struct item *pair);
  //@ requires [?f0]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub);
  /*@ ensures  [f0]world(pub, key_clsfy) &*& item(pair, p, pub) &*&
               p == pair_item(?fst, ?snd) &*&
               item(result, ?snd0, pub) &*&
               col ? true : snd == snd0; @*/

///////////////////////////////////////////////////////////////////////////////
// Nonce item /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_nonce(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == nonce_item(_, _, _) : true; @*/

void check_is_nonce(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == nonce_item(_, _, _); @*/

//@ predicate nonce_request(int principal, int info) = emp;

struct item *create_nonce();
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1) &*&
               item(result, ?i, pub) &*& info_for_item(i) == info &*&
               i == nonce_item(principal, count + 1, 0); @*/

void increment_nonce(struct item *item);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?i, pub) &*&
               i == nonce_item(?principal, ?count, ?inc0); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, ?i_inc, pub) &*&
               col ? true :
                 i_inc == nonce_item(principal, count, inc0 + 1) &&
                 info_for_item(i) == info_for_item(i_inc); @*/

void random_buffer(char* buffer, int size);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               chars_(buffer, size, _) &*&
               principal(?principal, ?count) &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               chars(buffer, size, _) &*&
               principal(principal, count + 1); @*/

int random_int();
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1); @*/

unsigned int random_u_int();
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [_]pub(nonce_item(principal, count + 1, 0)); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count + 1); @*/

///////////////////////////////////////////////////////////////////////////////
// Hash item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_hash(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == hash_item(_) : true; @*/

void check_is_hash(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == hash_item(_); @*/

struct item *create_hash(struct item *payload);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(payload, ?pay, pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(payload, pay, pub) &*& item(result, ?hash, pub) &*&
               col || hash == hash_item(some(pay)); @*/

///////////////////////////////////////////////////////////////////////////////
// Key item ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//Symmetric keys

bool is_symmetric_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == symmetric_key_item(_, _) : true; @*/

void check_is_symmetric_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == symmetric_key_item(_, _); @*/

//@ predicate key_request(int principal, int info) = emp;

struct item *create_symmetric_key();
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               key_request(?principal, ?info) &*&
               principal(principal, ?count); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               principal(principal, count + 1) &*&
               item(result, ?k, pub) &*&
               k == symmetric_key_item(principal, count + 1) &*&
               info == info_for_item(k); @*/

//Asymmetric keys

bool is_public_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == public_key_item(_, _) : true; @*/

void check_is_public_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == public_key_item(_, _); @*/

bool is_private_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == private_key_item(_, _) : true; @*/

void check_is_private_key(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == private_key_item(_, _); @*/

/*@

predicate keypair(struct keypair *keypair, int principal, int id, int info,
                  predicate(item) pub);

predicate keypair_request(int principal, int info) = emp;

@*/

struct keypair *create_keypair(int principal);
  /*@ requires world(?pub, ?key_clsfy) &*&
               keypair_request(principal, ?info) &*&
               principal(principal, ?count); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               keypair(result, principal, count + 1, info, pub) &*&
               principal(principal, count + 1); @*/

void keypair_free(struct keypair *keypair);
  //@ requires keypair(keypair, _, _, _, _);
  //@ ensures  true;

struct item *get_public_key(int participant);
  //@ requires [?f]world(?pub, ?key_clsfy);
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(result, ?key, pub) &*&
               key == public_key_item(participant, 1); @*/

/*@
lemma void info_for_asymmetric_keypair(item pub_key, item priv_key);
  requires pub_key == public_key_item(?p, ?c) &*&
           priv_key == private_key_item(p, c);
  ensures  info_for_item(pub_key) ==
           info_for_item(priv_key);
@*/

struct item *keypair_get_private_key(struct keypair *keypair);
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == private_key_item(creator, id) &*&
               info_for_item(key) == info; @*/

struct item *keypair_get_public_key(struct keypair *keypair);
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == public_key_item(creator, id) &*&
               info_for_item(key) == info; @*/

///////////////////////////////////////////////////////////////////////////////
// Hmac item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_hmac(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == hmac_item(_, _, _) : true; @*/

void check_is_hmac(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == hmac_item(_, _, _); @*/

struct item *create_hmac(struct item *key, struct item *payload);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(payload, ?pay, pub) &*&
               [?f2]item(key, ?k, pub) &*&
                 k == symmetric_key_item(?creator, ?id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(payload, pay, pub) &*& [f2]item(key, k, pub) &*&
               item(result, ?hmac, pub) &*&
               col || hmac == hmac_item(creator, id, some(pay)); @*/

///////////////////////////////////////////////////////////////////////////////
// Symmetric encrypted item ///////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_symmetric_encrypted(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == symmetric_encrypted_item(_, _, _, _) : true; @*/

void check_is_symmetric_encrypted(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == symmetric_encrypted_item(_, _, _, _); @*/

struct item *symmetric_encryption(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
                 [_]pub(nonce_item(principal1, count1 + 1, 0)) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
                 k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 2) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?enc, pub) &*&
               col ? true :
                 enc == symmetric_encrypted_item(principal2, count2,
                                                 some(pay), ?ent); @*/

struct item *symmetric_decryption(struct item *key, struct item *item);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
                 enc == symmetric_encrypted_item(?principal1, ?count1,
                                                 ?pay, ?ent) &*&
               k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*&
               item(result, ?dec, pub) &*&
               col ? [_]pub(dec) :
               switch(pay)
               {
                 case some(dec2):
                   return principal1 == principal2 &&
                          count1 == count2 && dec == dec2;
                 case none:
                   return false;
               }; @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric encrypted item //////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_asymmetric_encrypted(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == asymmetric_encrypted_item(_, _, _, _) : true; @*/

void check_is_asymmetric_encrypted(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == asymmetric_encrypted_item(_, _, _, _); @*/

struct item *asymmetric_encryption(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?enc, pub) &*&
               col ? true :
                 enc == asymmetric_encrypted_item(principal2, count2,
                                                  some(pay), _); @*/

#define TAG_DATA            'a'
#define TAG_PAIR            'b'
#define TAG_NONCE           'c'
#define TAG_HASH            'd'
#define TAG_SYMMETRIC_KEY   'e'
#define TAG_PUBLIC_KEY      'f'
#define TAG_PRIVATE_KEY     'g'
#define TAG_HMAC            'h'
#define TAG_SYMMETRIC_ENC   'i'
#define TAG_ASYMMETRIC_ENC  'j'
#define TAG_ASYMMETRIC_SIG  'k'

/*@

fixpoint char tag_for_item(item i)
{
  switch(i)
  {
    case data_item(cs0):                                return TAG_DATA;
    case pair_item(f0, s0):                             return TAG_PAIR;
    case nonce_item(p0, c0, inc0):                      return TAG_NONCE;
    case hash_item(pay0):                               return TAG_HASH;
    case symmetric_key_item(p0, c0):                    return TAG_SYMMETRIC_KEY;
    case public_key_item(p0, c0):                       return TAG_PUBLIC_KEY;
    case private_key_item(p0, c0):                      return TAG_PRIVATE_KEY;
    case hmac_item(p0, c0, pay0):                       return TAG_HMAC;
    case symmetric_encrypted_item(p0, c0, pay0, ent0):  return TAG_SYMMETRIC_ENC;
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return TAG_ASYMMETRIC_ENC;
    case asymmetric_signature_item(p0, c0, pay0, ent0): return TAG_ASYMMETRIC_SIG;
  }
}

fixpoint bool valid_tag(char tag)
{
  return tag == TAG_DATA ||
         tag == TAG_PAIR ||
         tag == TAG_NONCE ||
         tag == TAG_HASH ||
         tag == TAG_SYMMETRIC_KEY ||
         tag == TAG_PUBLIC_KEY ||
         tag == TAG_PRIVATE_KEY ||
         tag == TAG_HMAC ||
         tag == TAG_SYMMETRIC_ENC ||
         tag == TAG_ASYMMETRIC_ENC ||
         tag == TAG_ASYMMETRIC_SIG;
}

@*/

struct item *asymmetric_decryption(struct item *key, struct item *item, char tag);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& true == valid_tag(tag) &*&
               principal(?principal1, ?count1) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
                 enc == asymmetric_encrypted_item(?principal2, ?count2,
                                                  ?pay, ?ent) &*&
               k == private_key_item(?principal3, ?count3); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*&
               item(result, ?dec, pub) &*& tag_for_item(dec) == tag &*&
               col ?
                 [_]pub(dec)
               : principal2 != principal3 || count2 != count3 ?
                 true == key_clsfy(principal3, count3, false) &*&
                 [_]pub(dec)
               :
                 switch(pay)
                 {
                   case some(dec2):
                     return dec == dec2;
                   case none:
                     return false;
                 }; @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric signature item //////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_asymmetric_signature(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == asymmetric_signature_item(_, _, _, _) : true; @*/

void check_is_asymmetric_signature(struct item *item);
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == asymmetric_signature_item(_, _, _, _); @*/

struct item *asymmetric_signature(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
               k == private_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?sig, pub) &*&
               col ? true :
                 sig == asymmetric_signature_item(principal2, count2,
                                                  some(pay), _); @*/

void asymmetric_signature_verify(struct item *key, struct item *item,
                                 struct item *signature);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?i, pub) &*& item(key, ?k, pub) &*&
               item(signature, ?sig, pub) &*&
                 sig == asymmetric_signature_item(?principal1, ?count1,
                                                  ?pay1, ?ent) &*&
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, i, pub) &*& item(key, k, pub) &*&
               item(signature, sig, pub) &*&
               col ? true :
               switch(pay1)
               {
                 case some(pay2):
                   return principal1 == principal2 &&
                          count1 == count2 && pay2 == i;
                 case none:
                   return false;
               }; @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric authenticated encryption ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *asymmetric_authenticated_encryption(int recipient,
                                                 struct item *public_key,
                                                 struct item *private_key,
                                                 struct item *payload);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*&
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*&
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 2) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(payload, pay, pub) &*&
               item(result, ?msg, pub) &*&
               col ? true :
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(principal2, count2,
                                                  some(pay), _) &*&
                 sig == asymmetric_signature_item(principal3, count3,
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(chars_of_int(recipient)),
                                     hash_item(some(enc))); @*/

struct item *asymmetric_authenticated_decryption(int recipient, char tag,
                                                 struct item *public_key,
                                                 struct item *private_key,
                                                 struct item *message);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& true == valid_tag(tag) &*&
               principal(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*&
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*&
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(message, ?msg, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(message, msg, pub) &*&
               item(result, ?decrypted, pub) &*&
               col ? [_]pub(decrypted) :
                 tag_for_item(decrypted) == tag &*&
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(?principal4, ?count4,
                                                  ?pay, _) &*&
                 sig == asymmetric_signature_item(?principal5, ?count5,
                                                  some(?msg_id), _) &*&
                 principal3 != principal4 || count3 != count4 ?
                   true == key_clsfy(principal3, count3, false) &*&
                   [_]pub(decrypted)
                 :
                   msg_id == pair_item(data_item(chars_of_int(recipient)),
                                       hash_item(some(enc))) &*&
                   principal2 == principal5 && count2 == count5 &*&
                   switch(pay)
                   {
                     case some(pay2):
                       return pay2 == decrypted;
                     case none:
                       return false;
                   }; @*/

///////////////////////////////////////////////////////////////////////////////
// Network ////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct network_status;

//@ predicate network_status(struct network_status *stat);

void network_sleep(unsigned int microseconds);
  //@ requires true;
  //@ ensures  true;

struct network_status *network_connect(const char *name, int port);
  //@ requires [?f1]option_string(name, ?ip);
  //@ ensures  [f1]option_string(name, ip) &*& network_status(result);

struct network_status *network_bind_and_accept(int port);
  //@ requires true;
  //@ ensures  network_status(result);

void network_disconnect(struct network_status *stat);
  //@ requires network_status(stat);
  //@ ensures  true;

void network_send(struct network_status *stat, struct item *datagram);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& network_status(stat) &*&
               item(datagram, ?d, pub) &*& [_]pub(d); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               network_status(stat) &*&
               item(datagram, d, pub); @*/

struct item *network_receive(struct network_status *stat);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& network_status(stat); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& network_status(stat) &*&
               item(result, ?d, pub) &*& [_]pub(d); @*/

///////////////////////////////////////////////////////////////////////////////
// Proof obligations //////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

typedef lemma void key_classifier(predicate(item) pub,
                                  fixpoint(int, int, bool, bool) key_clsfy)
                                 (item key, int p, int c, bool symmetric);
  requires  [_]pub(key) &*&
            symmetric ?
              key == symmetric_key_item(p, c)
            :
              key == private_key_item(p, c);
  ensures   col || true == key_clsfy(p, c, symmetric);

predicate proof_obligations(predicate(item) pub) =
  is_public_collision(_, pub) &*&
  is_public_none_payload_item(_, pub) &*&
  is_public_data(_, pub) &*&
  is_public_pair_compose(_, pub) &*&
  is_public_pair_decompose(_, pub) &*&
  is_public_nonce(_, pub) &*&
  is_public_incremented_nonce(_, pub) &*&
  is_public_hash(_, pub) &*&
  is_public_symmetric_key(_, pub) &*&
  is_public_public_key(_, pub) &*&
  is_public_private_key(_, pub) &*&
  is_public_hmac(_, pub) &*&
  is_public_symmetric_encrypted(_, pub) &*&
  is_public_symmetric_encrypted_entropy(_, pub) &*&
  is_public_symmetric_decrypted(_, pub) &*&
  is_public_asymmetric_encrypted(_, pub) &*&
  is_public_asymmetric_encrypted_entropy(_, pub) &*&
  is_public_asymmetric_decrypted(_, pub) &*&
  is_public_asymmetric_signature(_, pub)
;

typedef lemma void public_collision(predicate(item) pub)(item i);
  requires  true == col;
  ensures   [_]pub(i);

typedef lemma void public_none_payload_item(predicate(item) pub)(item i);
  requires  true == none_payload_item(i);
  ensures   [_]pub(i);

typedef lemma void public_data(predicate(item) pub)(item data);
  requires  data == data_item(?d);
  ensures   [_]pub(data);

typedef lemma void public_pair_compose(predicate(item) pub)
                                      (item first, item second);
  requires  [_]pub(first) &*& [_]pub(second);
  ensures   [_]pub(pair_item(first, second));

typedef lemma void public_pair_decompose(predicate(item) pub)(item pair);
  requires  [_]pub(pair_item(?first, ?second));
  ensures   [_]pub(first) &*& [_]pub(second);

typedef lemma void public_nonce(predicate(item) pub)(item nonce);
  requires  nonce == nonce_item(?p, ?c, ?inc) &*& true == bad(p);
  ensures   [_]pub(nonce);

typedef lemma void public_incremented_nonce(predicate(item) pub)
                                           (item nonce1, item nonce2);
  requires  nonce1 == nonce_item(?p, ?c, ?inc1) &*&
            nonce2 == nonce_item(p, c, ?inc2) &*&
            [_]pub(nonce1);
  ensures   [_]pub(nonce2);

typedef lemma void public_hash(predicate(item) pub)(item hash);
  requires  hash == hash_item(?pay) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(hash);

typedef lemma void public_symmetric_key(predicate(item) pub)(item key);
  requires  key == symmetric_key_item(?p, _) &*& true == bad(p);
  ensures   [_]pub(key);

typedef lemma void public_public_key(predicate(item) pub)(item key);
  requires  key == public_key_item(_, _);
  ensures   [_]pub(key);

typedef lemma void public_private_key(predicate(item) pub)(item key);
  requires  key == private_key_item(?p, _) &*& true == bad(p);
  ensures   [_]pub(key);

typedef lemma void public_hmac(predicate(item) pub)(item hmac);
  requires  hmac == hmac_item(?p, ?c, ?pay) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(symmetric_key_item(p, c)) &*&
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(hmac);

typedef lemma void public_symmetric_encrypted(predicate(item) pub)(item enc);
  requires  enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(symmetric_key_item(p, c)) &*&
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(enc);

typedef lemma void public_symmetric_encrypted_entropy(predicate(item) pub)
                                                     (item enc, list<crypto_char> ent);
  requires  [_]pub(enc) &*&
            enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent0);
  ensures   [_]pub(symmetric_encrypted_item(p, c, pay, ent));

typedef lemma void public_symmetric_decrypted(predicate(item) pub)(item enc);
  requires  enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            [_]pub(enc) &*& [_]pub(symmetric_key_item(p, c));
  ensures   switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };

typedef lemma void public_asymmetric_encrypted(predicate(item) pub)(item enc);
  requires  enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(public_key_item(p, c)) &*&
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(enc);

typedef lemma void public_asymmetric_encrypted_entropy(predicate(item) pub)
                                                      (item enc, list<crypto_char> ent);
  requires  [_]pub(enc) &*&
            enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent0);
  ensures   [_]pub(asymmetric_encrypted_item(p, c, pay, ent));

typedef lemma void public_asymmetric_decrypted(predicate(item) pub)(item enc);
  requires  enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            [_]pub(enc) &*& [_]pub(private_key_item(p, c));
  ensures   switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };

typedef lemma void public_asymmetric_signature(predicate(item) pub)(item sig);
  requires  sig == asymmetric_signature_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(private_key_item(p, c)) &*&
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(sig);

@*/

///////////////////////////////////////////////////////////////////////////////
// Attacker ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
lemma void retreive_proof_obligations();
  nonghost_callers_only
  requires [?f]world(?pub, ?key_clsfy);
  ensures  [f]world(pub, key_clsfy) &*& proof_obligations(pub);
@*/

void symbolic_attacker(int attacker_id, struct keypair* keypair);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               true == bad(attacker_id) &*&
               principal(attacker_id, ?count) &*&
               keypair(keypair, attacker_id, ?id, ?info, pub); @*/
  //@ ensures  false;

///////////////////////////////////////////////////////////////////////////////
// Debugging //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void debug_print(const char *message);
  //@ requires [?f]string(message, ?cs);
  //@ ensures  [f]string(message, cs);

void print_buffer(const char *buffer, int size);
  //@ requires [?f]crypto_chars(?kind, buffer, size, ?ccs);
  //@ ensures  [f]crypto_chars(kind, buffer, size, ccs);

void print_item(const struct item* item);
  //@ requires [?f]item(item, ?i, ?pub);
  //@ ensures  [f]item(item, i, pub);

#endif
