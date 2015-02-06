
#ifndef KEY_ITEM_H
#define KEY_ITEM_H

#include "general.h"

void check_valid_symmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == 1 + GCM_KEY_SIZE;

void check_valid_asymmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == 1 + RSA_SERIALIZED_KEY_SIZE;

void set_public_key(pk_context *ctx, struct item *pub_key);
  /*@ requires pk_context_initialized(ctx) &*&
               item(pub_key, public_key_item(?principal, ?count), ?pub); @*/
  /*@ ensures  pk_context_with_key(ctx, pk_public, RSA_BIT_KEY_SIZE, ?id) &*&
               item(pub_key, public_key_item(principal, count), pub) &*&
               collision_in_run() ? 
                 true 
               : 
                 id == some(pair(principal, count)); @*/

void set_private_key(pk_context *ctx, struct item *priv_key);
  /*@ requires pk_context_initialized(ctx) &*&
               item(priv_key, private_key_item(?principal, ?count), ?pub); @*/
  /*@ ensures  pk_context_with_key(ctx, pk_private, RSA_BIT_KEY_SIZE, ?id) &*&
               item(priv_key, private_key_item(principal, count), pub) &*&
               collision_in_run() ? 
                 true 
               : 
                 id == some(pair(principal, count)); @*/

struct keypair
{
  struct item* public_key;
  struct item* private_key;
};

/*@ 

predicate keypair(struct keypair *keypair, int principal, int id, int info,
                  predicate(item) pub) =
  keypair->public_key |-> ?pub_k &*&
  keypair->private_key |-> ?pri_k &*&
  malloc_block_keypair(keypair) &*&
  
  item(pub_k, public_key_item(principal, id), pub) &*&
    [_]info_for_item(public_key_item(principal, id), info) &*&
  item(pri_k, private_key_item(principal, id), pub) &*&
    [_]info_for_item(private_key_item(principal, id), info)
;

@*/

#endif
