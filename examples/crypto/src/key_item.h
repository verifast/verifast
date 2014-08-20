
#ifndef KEY_ITEM_H
#define KEY_ITEM_H

#include "general.h"

// see ../include/cryptolib.h

//@ require_module key_item;

bool is_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return result == true;
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

//Symmetric keys

bool is_symmetric_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return true == if_no_collision(result == (k0 == symmetric_key));
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

void check_is_symmetric_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*&
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return item(item, key_item(p0, c0, k0, i0)) &*&
                   true == if_no_collision(k0 == symmetric_key);
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

void check_valid_symmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == AES_KEY_SIZE;

void check_valid_symmetric_key_item_chars_size(int cs_size);
  //@ requires true;
  //@ ensures  cs_size == AES_KEY_SIZE - 2 * sizeof(int);

void check_valid_asymmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == RSA_SERIALIZED_KEY_SIZE + sizeof(char) + 2 * sizeof(int);

void check_valid_asymmetric_key_item_chars_size(int cs_size);
  //@ requires true;
  //@ ensures  cs_size == RSA_SERIALIZED_KEY_SIZE + sizeof(char);

//Asymmetric keys

bool is_public_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return true == if_no_collision(result == (k0 == public_key));
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

void check_is_public_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*&
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return item(item, key_item(p0, c0, k0, i0)) &*&
                   true == if_no_collision(k0 == public_key);
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

bool is_private_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return true == if_no_collision(result == (k0 == private_key));
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

void check_is_private_key(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub) &*&
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return item(item, key_item(p0, c0, k0, i0)) &*&
                   true == if_no_collision(k0 == private_key);
          case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return false;
        };
  @*/

void set_public_key(pk_context *ctx, struct item *pub_key);
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               pk_context_initialized(ctx) &*&
               item(pub_key, key_item(?principal, ?count, public_key, ?info)); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               item(pub_key, key_item(principal, count, public_key, info)) &*&
               pk_context_with_key(ctx, ?principal2, ?count2, pk_public) &*&
               true == if_no_collision(
                 principal == principal2 && count == count2
               ); @*/

void set_private_key(pk_context *ctx, struct item *priv_key);
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               pk_context_initialized(ctx) &*&
               item(priv_key, key_item(?principal, ?count, private_key, ?info)); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               item(priv_key, key_item(principal, count, private_key, info)) &*&
               pk_context_with_key(ctx, ?principal2, ?count2, pk_private) &*&
               true == if_no_collision(
                 principal == principal2 && count == count2
               ); @*/

struct keypair
{
  struct item* public_key;
  struct item* private_key;
};

/*@ 

predicate keypair(struct keypair *keypair, int principal, int id, int info) =
  keypair->public_key |-> ?pub_k &*&
  keypair->private_key |-> ?pri_k &*&
  malloc_block_keypair(keypair) &*&
  
  item(pub_k, key_item(principal, id, public_key, info)) &*&
  item(pri_k, key_item(principal, id, private_key, info))
;

predicate key_registry_initialized();

@*/

void key_registry_init();
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               module(key_item, true); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*& 
               key_registry_initialized(); @*/

void key_registry_exit();
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               key_registry_initialized(); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*& 
               module(key_item, false); @*/

#endif
