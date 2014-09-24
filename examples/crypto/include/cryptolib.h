#ifndef CRYPTOLIB_H
#define CRYPTOLIB_H

#include "shared_definitions.h"
#include "aux_include/attacker_proof_obligations.gh"
#include "aux_include/switch_primitives.gh"

#include <pthread.h>

///////////////////////////////////////////////////////////////////////////////
// Module stuff ///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ require_module cryptolib;

///////////////////////////////////////////////////////////////////////////////
// Principals /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
predicate principal(int p);

predicate principals_created(int p);

predicate initial_principals() = principals_created(0);

predicate generated_values(int principal, int count);

fixpoint bool bad(int principal);
@*/

int create_principal();
  //@ requires [?f]world(?pub) &*& principals_created(?count);
  /*@ ensures  [f]world(pub) &*& principals_created(count + 1) &*& 
               principal(count + 1) &*& generated_values(count + 1, 0) &*&
               result == count + 1; @*/

/*@
lemma void destroy_principal(int count);
  requires [?f]world(?pub) &*& principal(count) &*&
           generated_values(count, _);
  ensures  [f]world(pub);
@*/

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate world(fixpoint(item, bool) pub);

@*/

void init_crypto_lib();
  /*@ requires module(cryptolib, true) &*&
               exists<fixpoint(item, bool)>(?pub);
  @*/
  //@ ensures  world(pub) &*& initial_principals();

void abort_crypto_lib(const char* message);
  //@ requires [?f]string(message, ?cs);
  //@ ensures  false;

void exit_crypto_lib();
  //@ requires world(?pub) &*& principals_created(_);
  //@ ensures  module(cryptolib, false);

///////////////////////////////////////////////////////////////////////////////
// Item ///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item;

/*@

inductive key_kind =
  | symmetric_key
  | public_key
  | private_key;

fixpoint key_kind inverse_key_kind(key_kind k)
{
  switch(k)
  {
    case symmetric_key: return symmetric_key;
    case public_key: return private_key;
    case private_key: return public_key;
  }
}

inductive item =
  | data_item      (int i)
  | pair_item      (item first, item second)
  | nonce_item     (int principal, int count, int inc, int info)
  | key_item       (int principal, int count, key_kind kind, int info)
  | hmac_item      (item key, item payload)
  | encrypted_item (item key, item payload, list<char> entropy);

predicate item(struct item *item, item i);

@*/

void item_free(struct item* item);
  //@ requires item(item, _);
  //@ ensures  emp;

struct item* item_clone(struct item* item);
  //@ requires [?f]item(item, ?i);
  //@ ensures  [f]item(item, i) &*& item(result, i) &*& result != 0;

bool item_equals(struct item *item1, struct item *item2);
  /*@ requires [?f0]world(?pub) &*&
               [?f2]item(item1, ?i1) &*& [?f3]item(item2, ?i2); @*/
  /*@ ensures  [f0]world(pub) &*&
               [f2]item(item1, i1) &*& [f3]item(item2, i2) &*&
               true == if_no_collision(result == (i1 == i2));
  @*/

///////////////////////////////////////////////////////////////////////////////
// Data item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_data_item(int data);
  //@ requires [?f]world(?pub);
  //@ ensures  [f]world(pub) &*& item(result, data_item(data));

void check_is_data(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return item(item, i);
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

int item_get_data(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return item(item, i) &*& true == if_no_collision(result == d0);
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

///////////////////////////////////////////////////////////////////////////////
// Pair item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_pair(struct item *first, struct item *second);
  /*@ requires [?f]world(?pub) &*&
               item(first, ?fi) &*& item(second, ?si);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(first, fi) &*& item(second, si) &*&
               item(result, pair_item(fi, si));
  @*/

void check_is_pair(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(item, i);
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

struct item *pair_get_first(struct item *pair);
  //@ requires item(pair, ?p);
  /*@ ensures  item(pair, p) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(result, ?f1) &*& 
                   true == if_no_collision(f0 == f1);
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

struct item *pair_get_second(struct item *pair);
  //@ requires item(pair, ?p);
  /*@ ensures  item(pair, p) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(result, ?s1) &*& 
                   true == if_no_collision(s0 == s1);
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

///////////////////////////////////////////////////////////////////////////////
// Nonce item /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate nonce_request(int principal, int info) = emp;

@*/

struct item *create_nonce();
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?i) &*&
               i == nonce_item(principal, count + 1, 0, info); 
  @*/

void check_is_nonce(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return item(item, nonce_item(p0, c0, inc0, i0));
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

void increment_nonce(struct item *item);
  /*@ requires [?f]world(?pub) &*& item(item, ?ni) &*& 
               ni == nonce_item(?principal, ?count, ?inc0, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*& item(item, ?i) &*& 
               i == nonce_item(principal, count, inc0 + 1, info);
  @*/

void random_buffer(char* buffer, int size);
  /*@ requires [?f]world(?pub) &*&
               chars(buffer, size, _) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               chars(buffer, size, _) &*&
               generated_values(principal, count + 1); @*/

int random_int();
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1); @*/

///////////////////////////////////////////////////////////////////////////////
// Key item ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//check_is_key aborts if the item is not a key.
void check_is_key(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures 
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return item(item, key_item(p0, c0, k0, i0));
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

//Symmetric keys

//@ predicate key_request(int principal, int info) = emp;

struct item *create_symmetric_key();
  /*@ requires [?f]world(?pub) &*&
               key_request(?principal, ?info) &*&
               generated_values(principal, ?count);
  @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?k) &*&
               k == key_item(principal, count + 1, symmetric_key, info);
  @*/

//Asymmetric keys

struct keypair;
//@ predicate keypair(struct keypair *keypair, int principal, int id, int info);
//@ predicate keypair_request(int principal, int info) = emp;

struct keypair *create_keypair(int principal);
  /*@ requires world(?pub) &*&
               keypair_request(principal, ?info) &*&
               generated_values(principal, ?count);
  @*/
  /*@ ensures  world(pub) &*&
               generated_values(principal, count + 1) &*&
               keypair(result, principal, count + 1, info);
  @*/

void keypair_free(struct keypair *keypair);
  /*@ requires [?f]world(?pub) &*&
               keypair(keypair, ?principal, ?count, ?info);
  @*/
  //@ ensures  [f]world(pub);

struct item *get_public_key(int participant);
  //@ requires [?f]world(?pub);
  /*@ ensures  [f]world(pub) &*&
               item(result, key_item(participant, _, public_key, _));
  @*/

struct item *keypair_get_private_key(struct keypair *keypair);
  //@ requires [?f]world(?pub) &*& keypair(keypair, ?creator, ?id, ?info);
  /*@ ensures  [f]world(pub) &*& keypair(keypair, creator, id, info) &*&
               item(result, key_item(creator, id, private_key, info));
  @*/

struct item *keypair_get_public_key(struct keypair *keypair);
  //@ requires [?f]world(?pub) &*& keypair(keypair, ?creator, ?id, ?info);
  /*@ ensures  [f]world(pub) &*&
               item(result, key_item(creator, id, public_key, info));
  @*/

///////////////////////////////////////////////////////////////////////////////
// Hmac item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *hmac(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?p) &*& item(key, ?k) &*& 
               k == key_item(?creator, ?id, ?kind, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, p) &*& item(key, k) &*& 
               item(result, ?hmac) &*& hmac == hmac_item(k, p);
  @*/

void hmac_verify(struct item *hash, struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               item(hash, ?h) &*& item(payload, ?p) &*&
               item(key, key_item(?creator, ?id, ?kind, ?info));
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(hash, h) &*& item(payload, p) &*&
               item(key, key_item(creator, id, kind, info)) &*&
               true == if_no_collision(
                 h == hmac_item(key_item(creator, id, kind, info), p)); @*/

//check_is_hmac aborts if the item is not a hmac.
void check_is_hmac(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
         case hmac_item(key0, pay0):
            return item(item, hmac_item(key0, pay0));
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

///////////////////////////////////////////////////////////////////////////////
// Encrypted item /////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// This function aborts if the key is not a symmetric or public key item.
struct item *encrypt(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*& item(key, ?key_i) &*& 
               key_i == key_item(?s, ?count1, ?kind, ?info) &*&
               item(payload, ?pay_i) &*&
               generated_values(?principal, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*& item(key, key_item(s, count1, kind, info)) &*&
               item(payload, pay_i) &*&
               generated_values(principal, count2 + 1) &*&
               item(result, encrypted_item(?key_enc, ?pay_enc, ?entropy)) &*&
               true == if_no_collision(key_enc == key_i && pay_enc == pay_i);
  @*/

void check_is_encrypted(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
         case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return item(item, encrypted_item(key0, pay0, ent0));
        };
  @*/

// This function aborts if the key is not a symmetric or private key item.
struct item *decrypt(struct item *key, struct item *item);
  /*@ requires [?f]world(?pub) &*& item(item, ?i) &*&
               item(key, ?key_i) &*&
               key_i == key_item(?participant, ?count, ?kind, ?info) &*&
               generated_values(?principal, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
               item(key, key_i) &*&
               generated_values(principal, ?count3) &*& count3 >= count2 &*&
               switch (i)
               {
                 case nonce_item(p0, c0, inc0, i0): return false;
                 case key_item(p0, c0, k0, i0): return false;
                 case data_item(d0): return false;
                 case hmac_item(k0, payload0): return false;
                 case encrypted_item(key0, pay0, ent0): return
                     item(result, ?resulti) &*&
                     true == if_no_collision(
                       resulti == pay0 && 
                       key0 == key_item(participant, count, 
                                        inverse_key_kind(kind), info) 
                     );
                 case pair_item(f0, s0): return false;
               };
  @*/

///////////////////////////////////////////////////////////////////////////////
// Network ////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct network_status;

//@ predicate network_status(struct network_status *stat);

void network_sleep(unsigned int microseconds);
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub);

struct network_status *network_connect(const char *name, int port);
  /*@ requires [?f0]world(?pub) &*&
               [?f1]string(name, ?cs); @*/
  /*@ ensures  [f0]world(pub) &*&
               [f1]string(name, cs) &*& network_status(result); @*/

struct network_status *network_bind_and_accept(int port);
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub) &*& network_status(result);

void network_disconnect(struct network_status *stat);
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  //@ ensures  [f0]world(pub);

void network_send(struct network_status *stat, struct item *datagram);
  /*@ requires [?f0]world(?pub) &*& network_status(stat) &*&
               item(datagram, ?d) &*& true == if_no_collision(pub(d)); @*/
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               item(datagram, d); @*/

struct item *network_receive(struct network_status *stat);
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               item(result, ?d) &*& true == if_no_collision(pub(d)); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
predicate attacker_proof_obligations(fixpoint(item, bool) pub) =
 is_can_send_data(_, pub) &*&
 is_can_send_public_pair(_, pub) &*&
 is_can_send_decomposed_public_pair(_, pub) &*&
 is_can_send_bad_principal_nonce(_, pub) &*&
 is_can_send_incremented_nonce(_, pub) &*&
 is_can_send_bad_principal_keys(_, pub) &*&
 is_can_send_public_hmac(_, pub) &*&
 is_can_send_public_encrypted(_, pub) &*& 
 is_can_send_public_decrypted(_, pub);

typedef lemma void can_send_data(fixpoint(item, bool) pub)(int data);
  requires  [?f0]world(pub);
  ensures   [f0]world(pub) &*&
            pub(data_item(data)) == true;

typedef lemma void can_send_public_pair(fixpoint(item, bool) pub)
                                       (struct item* first, struct item* second);
  requires  [?f0]world(pub) &*&
            item(first, ?f_item) &*& item(second, ?s_item) &*&
            true == if_no_collision(
              pub(f_item) && pub(s_item)
            );
  ensures   [f0]world(pub) &*&
            item(first, f_item) &*& item(second, s_item) &*&
            true == if_no_collision(
              pub(pair_item(f_item, s_item)) == true
            );

typedef lemma void can_send_decomposed_public_pair(fixpoint(item, bool) pub)
                                                  (struct item* pair);
  requires  [?f0]world(pub) &*&
            item(pair, pair_item(?i1, ?i2)) &*&
            true == if_no_collision(
              pub(pair_item(i1, i2)) == true
            );
  ensures   [f0]world(pub) &*&
            item(pair, pair_item(i1, i2)) &*&
            true == if_no_collision(
              pub(i1) && pub(i2)
            );

typedef lemma void can_send_bad_principal_nonce(fixpoint(item, bool) pub)
                                               (struct item* nonce);
  requires  [?f0]world(pub) &*&
            item(nonce, nonce_item(?p, ?c, ?inc, ?i)) &*&
            bad(p) == true;
  ensures   [f0]world(pub) &*&
            item(nonce, nonce_item(p, c, inc, i)) &*&
            pub(nonce_item(p, c, inc, i)) == true;

typedef lemma void can_send_incremented_nonce(fixpoint(item, bool) pub)
                                             (struct item* nonce);
  requires  [?f0]world(pub) &*&
            item(nonce, ?ni) &*& ni == nonce_item(?p, ?c, ?inc, ?i) &*&
            true == if_no_collision(
              pub(ni) == true
            );
  ensures   [f0]world(pub) &*&
            item(nonce, ni) &*&
            true == if_no_collision(
              pub(nonce_item(p, c, inc + 1, i)) == true
            );

typedef lemma void can_send_bad_principal_keys(fixpoint(item, bool) pub)(int p);
  requires  [?f0]world(pub) &*&
            item(?item, key_item(p, ?c, ?k, ?i)) &*&
            bad(p) == true;
  ensures   [f0]world(pub) &*&
            item(item, key_item(p, c, k, i)) &*&
            pub(key_item(p, c, k, i)) == true;

typedef lemma void can_send_public_hmac(fixpoint(item, bool) pub)
                                       (struct item* key, 
                                        struct item* payload,
                                        struct item* hmac);
  requires  [?f0]world(pub) &*&
            item(key, ?k_item) &*& k_item == key_item(?p, ?c, ?k, ?i) &*&
            item(payload, ?p_item) &*& item(hmac, ?h_item) &*&
            true == if_no_collision(
              h_item == hmac_item(k_item, p_item) &&
              pub(k_item) && pub(p_item)
            );
  ensures   [f0]world(pub) &*&
            item(key, k_item) &*& item(payload, p_item) &*&
            item(hmac, h_item) &*&
            true == if_no_collision(
              pub(h_item) == true
            );
 
typedef lemma void can_send_public_encrypted(fixpoint(item, bool) pub)
                                            (struct item* key, 
                                             struct item* payload,
                                             struct item* encrypted);
  requires  [?f0]world(pub) &*&
            item(key, ?k_item) &*& k_item == key_item(?p, ?c, ?k, ?i) &*&
            item(payload, ?p_item) &*&
            item(encrypted, ?e_item) &*&
            e_item == encrypted_item(?k_item', ?p_item', ?e) &*&
            true == if_no_collision(
              pub(k_item) == true && pub(p_item) == true &&
              k_item == k_item' && p_item == p_item'
            ); 
  ensures   [f0]world(pub) &*&
            item(key, k_item) &*& item(payload, p_item) &*&
            item(encrypted, e_item) &*&
            true == if_no_collision(
              pub(e_item) == true
            );

typedef lemma void can_send_public_decrypted(fixpoint(item, bool) pub)
                                            (struct item* key,
                                             struct item* payload,
                                             struct item* encrypted);
  requires  [?f0]world(pub) &*&
            item(key, ?k_item) &*&
              k_item == key_item(?p, ?c, ?k, ?i) &*&
            item(encrypted, ?e_item) &*&
              e_item == encrypted_item(?enc_key, ?enc_pay, _) &*&
            item(payload, ?p_item) &*&
            true == if_no_collision(
              pub(k_item) == true &&
              pub(e_item) == true &&
              enc_key == key_item(p, c, inverse_key_kind(k), i) && 
              p_item == enc_pay
            );
  ensures   [f0]world(pub) &*&
            item(key, k_item) &*& item(encrypted, e_item) &*&
            item(payload, p_item) &*&
            true == if_no_collision(
              pub(p_item) == true
            );
@*/

void attacker();
  /*@ requires exists<fixpoint(item, bool)>(?pub) &*&
               [?f0]world(pub) &*&
               attacker_proof_obligations(pub) &*&
               principals_created(_);
  @*/
  //@ ensures false;

///////////////////////////////////////////////////////////////////////////////
// Debugging //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void debug_print(const char *message);
  //@ requires [?f1]string(message, ?cs);
  //@ ensures  [f1]string(message, cs);

void print_buffer(const char *buffer, int size);
  //@ requires [?f1]chars(buffer, size, ?cs) &*& size < INT_MAX;
  //@ ensures  [f1]chars(buffer, size, cs);

void print_item(const struct item* item);
  //@ requires [?f1]item(item, ?i);
  //@ ensures  [f1]item(item, i);

#endif
