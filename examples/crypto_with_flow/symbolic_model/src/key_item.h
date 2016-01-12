
#ifndef KEY_ITEM_H
#define KEY_ITEM_H

#include "general.h"
#include "item_constraints.h"

void check_valid_symmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == TAG_LENGTH + GCM_KEY_SIZE;

void check_valid_asymmetric_key_item_size(int size);
  //@ requires true;
  //@ ensures  size == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE;

void set_public_key(pk_context *ctx, struct item *pub_key);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               pk_context_initialized(ctx) &*&
               item(pub_key, public_key_item(?principal, ?count), pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               pk_context_with_key(ctx, pk_public, ?p1, ?c1, RSA_BIT_KEY_SIZE) &*&
               item(pub_key, public_key_item(principal, count), pub) &*&
               col || p1 == principal && c1 == count; @*/

void set_private_key(pk_context *ctx, struct item *priv_key);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               pk_context_initialized(ctx) &*&
               item(priv_key, private_key_item(?principal, ?count), pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               pk_context_with_key(ctx, pk_private, ?p1, ?c1, RSA_BIT_KEY_SIZE) &*&
               item(priv_key, private_key_item(principal, count), pub) &*&
               col || p1 == principal && c1 == count; @*/
               
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
  item(pri_k, private_key_item(principal, id), pub) &*&
  info == info_for_item(public_key_item(principal, id)) &*&
  info == info_for_item(private_key_item(principal, id))
;

@*/

#endif
