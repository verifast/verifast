#include "key_item.h"

#include "principals.h"
#include "item.h"

#include "limits.h"

bool is_key(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
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
{
  //@ open item(item, i);
  return (item->tag == 3);
  //@ close item(item, i);
}

void check_is_key(struct item *item)
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
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  if (!is_key(item))
    abort_crypto_lib("Presented item is not a key");
}

//Symmetric keys

bool is_symmetric_key(struct item *item)
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
          case hmac_item(key0, pay0):
            return result == false;
          case encrypted_item(key0, pay0, ent0):
            return result == false;
        };
  @*/
{
  if (!is_key(item))
    return false;
    
  //@ open item(item, key_item(?p, ?c, ?k, ?info));
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  //@ open chars(cont, size, ?cs);
  /*@
      switch (k)
      {
        case symmetric_key:
          assert true;
        case public_key:
          assert true;
        case private_key:
          assert true;
      }
  @*/
  return *(item->content) == 'a';
  //@ close item(item, key_item(p, c, k, info));
}

void check_is_symmetric_key(struct item *item)
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
{
  if (!is_symmetric_key(item))
    abort_crypto_lib("Presented item is not a symmetric key");
}

void check_valid_symmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == AES_KEY_SIZE;
{
  if (size != AES_KEY_SIZE)
    abort_crypto_lib("Illegal size for key item");
}

void check_valid_symmetric_key_item_chars_size(int cs_size)
  //@ requires true;
  //@ ensures  cs_size == AES_KEY_SIZE - 2 * sizeof(int);
{
  if (cs_size != AES_KEY_SIZE - 2 * (int) sizeof(int))
    abort_crypto_lib("Illegal size for key item");
}

void check_valid_asymmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == RSA_SERIALIZED_KEY_SIZE + sizeof(char) + 2 * sizeof(int);
{
  if (size != RSA_SERIALIZED_KEY_SIZE + (int) sizeof(char)
                                      + 2 * (int) sizeof(int))
    abort_crypto_lib("Illegal size for key item");
}

void check_valid_asymmetric_key_item_chars_size(int cs_size)
  //@ requires true;
  //@ ensures  cs_size == RSA_SERIALIZED_KEY_SIZE + sizeof(char);
{
  if (cs_size != RSA_SERIALIZED_KEY_SIZE + (int) sizeof(char))
    abort_crypto_lib("Illegal size for key item");
}

struct item *create_symmetric_key()
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count) &*&
               key_request(principal, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*& 
               generated_values(principal, count + 1) &*&
               item(result, key_item(principal, count + 1, symmetric_key, info));
  @*/
{
  struct item* key = malloc(sizeof(struct item));
  if (key == 0){abort_crypto_lib("malloc of item failed");}
  key->tag = 3;
  key->size = AES_KEY_SIZE - 2 * (int) sizeof(int);
  key->content = malloc_wrapper(key->size);
  //@ open key_request(principal, info);
  //@ close nonce_request(principal, info);
  *(key->content) = 'a';
  create_havege_random(key->content + (int) sizeof(char), key->size - (int) sizeof(char));
  
  //@ open [f]world(pub);
  //@ havege_polarssl_item_to_chars(key->content + (int) sizeof(char));
  //@ close item(key, key_item(principal, count + 1, symmetric_key, info));
  return key;
  //@ close [f]world(pub);
}

//Asymmetric keys

bool is_public_key(struct item *item)
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
          case hmac_item(key0, pay0):
            return result == false;
          case encrypted_item(key0, pay0, ent0):
            return result == false;
        };
  @*/
{
  if (!is_key(item))
    return false;

  //@ open item(item, key_item(?p, ?c, ?k, ?info));
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  //@ open chars(cont, size, ?cs);
  /*@
      switch (k)
      {
        case symmetric_key:
          assert true;
        case public_key:
          assert true;
        case private_key:
          assert true;
      }
  @*/
  return *(item->content) == 'b';
  //@ close item(item, key_item(p, c, k, info));
}

void check_is_public_key(struct item *item)
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
{
  if (!is_public_key(item))
    abort_crypto_lib("Presented item is not a public key");
}

bool is_private_key(struct item *item)
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
          case hmac_item(key0, pay0):
            return result == false;
          case encrypted_item(key0, pay0, ent0):
            return result == false;
        };
  @*/
{
  if (!is_key(item))
    return false;
    
  //@ open item(item, key_item(?p, ?c, ?k, ?info));
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  //@ open chars(cont, size, ?cs);
  /*@
      switch (k)
      {
        case symmetric_key:
          assert true;
        case public_key:
          assert true;
        case private_key:
          assert true;
      }
  @*/
  return *(item->content) == 'c';
  //@ close item(item, key_item(p, c, k, info));
}

void check_is_private_key(struct item *item)
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
{
  if (!is_private_key(item))
    abort_crypto_lib("Presented item is not a public key");
}

int key_item_havege_random_stub(void *havege_state, 
                                     char *output, size_t len)
  /*@ requires
        [?f0]polarssl_world<item>(?pub) &*&
        [?f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(?principal, ?count) &*&
        havege_request(principal, ?info) &*&
        chars(output, len, _);
  @*/
  /*@ ensures
        [f0]polarssl_world<item>(pub) &*&
        [f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(principal, count + 1) &*&
        polarssl_item(output, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i); @*/
{
  return havege_random(havege_state, output, len);
}

void retreive_keys(pk_context *ctx, struct item **public, struct item **private)
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               pk_context_with_keys(ctx, ?principal, ?count, ?info) &*&
               pointer(public, _) &*& pointer(private, _); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               pk_context_with_keys(ctx, principal, count, info) &*&
               pointer(public, ?pub_key) &*& pointer(private, ?priv_key) &*&
               item(pub_key, key_item(principal, count, public_key, info)) &*&
               item(priv_key, key_item(principal, count, private_key, info)); @*/
{
  struct item* pub_i = malloc(sizeof(struct item));
  struct item* priv_i = malloc(sizeof(struct item));
  if (pub_i == 0 || priv_i == 0) {abort_crypto_lib("Malloc failed");}

  pub_i->tag = 3;
  pub_i->size = (int) sizeof(char) + RSA_SERIALIZED_KEY_SIZE;
  pub_i->content = malloc(pub_i->size);
  if (pub_i->content == 0) {abort_crypto_lib("Malloc failed");} 
  priv_i->tag = 3;
  priv_i->size = (int) sizeof(char) + RSA_SERIALIZED_KEY_SIZE;
  priv_i->content = malloc(priv_i->size);
  if (priv_i->content == 0) {abort_crypto_lib("Malloc failed");} 

  *(pub_i->content)  = 'b';
  *(priv_i->content) = 'c';
  
  if (pk_write_pubkey_pem(ctx, pub_i->content + (int) sizeof(char), 
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_pubkey_pem");
  }
  if (pk_write_key_pem(ctx, priv_i->content + (int) sizeof(char), 
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_key_pem");
  }
  
  //@ assert pub_i->content |-> ?cont;
  //@ assert polarssl_item(cont + sizeof(char), ?pi);
  //@ assert pi == polarssl_rsa_public_key_item(?p, ?c);
  //@ assert (info == info_for_polarssl_item(pi));
  //@ rsa_public_key_polarssl_item_to_chars(pub_i->content + sizeof(char));
  //@ close item(pub_i, key_item(principal, count, public_key, info));
  
  //@ rsa_private_key_polarssl_item_to_chars(priv_i->content + (int) sizeof(char));
  //@ close item(priv_i, key_item(principal, count, private_key, info));
  
  *public = pub_i;
  *private = priv_i;
}

void set_public_key(pk_context *ctx, struct item *pub_key)
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               pk_context_initialized(ctx) &*&
               item(pub_key, key_item(?principal, ?count, public_key, ?info)); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               item(pub_key, key_item(principal, count, public_key, info)) &*&
               pk_context_with_key(ctx, ?principal2, ?count2, pk_public) &*&
               true == if_no_collision(
                 principal == principal2 && count == count2
               ); @*/
{
  //@ open item(pub_key, key_item(principal, count, public_key, info));
  check_valid_asymmetric_key_item_chars_size(pub_key->size);
  
  //@ assert pub_key->content |-> ?cont;
  //@ chars_limits(pub_key->content);
  //@ chars_split(pub_key->content, sizeof(char));
  //@ rsa_public_key_chars_to_polarssl_item(pub_key->content + sizeof(char));
  //@ assert polarssl_item(cont + sizeof(char), ?pi);
  /*@ rsa_public_key_chars_for_polarssl_item_injective(
                       polarssl_rsa_public_key_item(principal, count), pi); @*/
  if (pk_parse_public_key(ctx, (void*) pub_key->content + (int) sizeof(char), 
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not set public key context");
  }
  //@ rsa_public_key_polarssl_item_to_chars(pub_key->content + sizeof(char));
  //@ close item(pub_key, key_item(principal, count, public_key, info));
}

void set_private_key(pk_context *ctx, struct item *priv_key)
  /*@ requires [?f]polarssl_world<item>(?pub) &*&
               pk_context_initialized(ctx) &*&
               item(priv_key, key_item(?principal, ?count, private_key, ?info)); @*/
  /*@ ensures  [f]polarssl_world<item>(pub) &*&
               item(priv_key, key_item(principal, count, private_key, info)) &*&
               pk_context_with_key(ctx, ?principal2, ?count2, pk_private) &*&
               true == if_no_collision(
                 principal == principal2 && count == count2
               ); @*/
{
  //@ open item(priv_key, key_item(principal, count, private_key, info));
  check_valid_asymmetric_key_item_chars_size(priv_key->size);
  
  //@ assert priv_key->content |-> ?cont;
  //@ chars_limits(priv_key->content);
  //@ chars_split(priv_key->content, sizeof(char));
  //@ rsa_private_key_chars_to_polarssl_item(priv_key->content + sizeof(char));
  //@ assert polarssl_item(cont + sizeof(char), ?pi);
  /*@ rsa_private_key_chars_for_polarssl_item_injective(
                       polarssl_rsa_private_key_item(principal, count), pi); @*/
  if (pk_parse_key(ctx, (void*) priv_key->content + (int) sizeof(char),
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE), 0, 0) != 0)
  {
    abort_crypto_lib("Could not set private key context");
  }
  //@ rsa_private_key_polarssl_item_to_chars(priv_key->content + sizeof(char));
  //@ close item(priv_key, key_item(principal, count, private_key, info));
}

void keypair_free(struct keypair *keypair)
  /*@ requires [?f]world(?pub) &*&
               keypair(keypair, ?principal, ?count, ?info);
  @*/
  //@ ensures  [f]world(pub);
{
  //@ open keypair(keypair, _, _, _);
  item_free(keypair->private_key);
  item_free(keypair->public_key);
  free(keypair);
}

struct item *keypair_get_private_key(struct keypair *keypair)
  //@ requires [?f]world(?pub) &*& keypair(keypair, ?creator, ?id, ?info);
  /*@ ensures  [f]world(pub) &*& keypair(keypair, creator, id, info) &*&
               item(result, key_item(creator, id, private_key, info));
  @*/
{
  //@ open keypair(keypair, creator, id, info);
  return item_clone(keypair->private_key);
  //@ close keypair(keypair, creator, id, info);
}

struct item *keypair_get_public_key(struct keypair *keypair)
  //@ requires [?f]world(?pub) &*& keypair(keypair, ?creator, ?id, ?info);
  /*@ ensures  [f]world(pub) &*&
               item(result, key_item(creator, id, public_key, info));
  @*/
{
  //@ open keypair(keypair, creator, id, info);
  struct item *key_pub = item_clone(keypair->public_key);
  //@ close keypair(keypair, creator, id, info);
  keypair_free(keypair);

  return key_pub;
}

struct key_registry
{
  int participant;
  struct item* pub_key;
  struct key_registry* next;
};

struct key_registry *registered_keys = 0;

/*@

predicate key_registry(struct key_registry *node) =
  node == 0 ?
    true
  :
    node->next |-> ?next &*&
      key_registry(next) &*&
    node->participant |-> ?participant &*&
    node->pub_key |-> ?key &*&
      item(key, key_item(participant, ?c, public_key, ?i)) &*&
      key != 0 &*&
    malloc_block_key_registry(node)
;

predicate key_registry_initialized() =
  pointer(&registered_keys, ?head) &*&
  key_registry(head)
;

@*/

void key_registry_init()
  /*@ requires module(key_item, true); @*/
  /*@ ensures  key_registry_initialized(); @*/
{
  //@ open_module();
  registered_keys = 0;
  //@ close key_registry(0);
  //@ close key_registry_initialized();
}

void clear_key_registry(struct key_registry* head)
  /*@ requires key_registry(head); @*/
  /*@ ensures  emp; @*/
{
  //@ open key_registry(head);
  if (head != 0)
  {
    clear_key_registry(head->next);
    item_free(head->pub_key);
    free(head);
  }
}

void key_registry_exit()
  /*@ requires key_registry_initialized(); @*/
  /*@ ensures  module(key_item, false); @*/
{
  //@ open key_registry_initialized();
  clear_key_registry(registered_keys);
  registered_keys = 0;
  //@ close_module();
}

void register_public_key(int participant, struct item *key)
  /*@ requires world(?pub) &*& key != 0 &*&
               item(key, key_item(participant, ?c, public_key, ?i)); @*/
  /*@ ensures  world(pub) &*&
               item(key, key_item(participant, c, public_key, i)); @*/
{
  struct item* clone = item_clone(key);

  //@ open world(pub);
  struct key_registry *kr = malloc(sizeof(struct key_registry));
  if (kr == 0) {abort_crypto_lib("malloc failed");}
 
  //@ open key_registry_initialized();
  kr->participant = participant;
  kr->pub_key = clone;
  kr->next = registered_keys;
  registered_keys = kr;
  
  //@ assert pointer(&registered_keys, ?head);
  //@ close key_registry(head);
  //@ close key_registry_initialized();
  //@ close world(pub);
}

struct item *get_public_key(int participant)
  //@ requires [?f]world(?pub);
  /*@ ensures  [f]world(pub) &*&
               item(result, key_item(participant, _, public_key, _));
  @*/
{
  //@ open [f]world(pub);
  //@ open [f]key_registry_initialized();
  
  if (participant < 1)
    abort_crypto_lib("Participant does not exist");
  
  struct item *result = 0;
  struct key_registry* current = registered_keys;
  while(current != 0 && result == 0)
   /*@ requires  [f]key_registry(current) &*& 
                 result == 0 ?
                   true 
                 : 
                   item(result, key_item(participant, _, public_key, _)); @*/
   /*@ ensures   [f]key_registry(old_current) &*& 
                 result == 0 ?
                   true 
                 : 
                   item(result, key_item(participant, _, public_key, _)); @*/
  {
    //@ open [f]key_registry(current);
    if (current->participant == participant)
    {
      result = item_clone(current->pub_key);
      //@ close [f]key_registry(old_current);
      break;
    }
    current = current->next;
    
    //@ recursive_call();
    //@ close [f]key_registry(old_current);
  }
  
  if (result == 0)
    abort_crypto_lib("Participant does not exist");
    
  return result;
  //@ close [f]key_registry_initialized();
  //@ close [f]world(pub);
}

struct keypair *create_keypair(int principal)
  /*@ requires world(?pub) &*&
               keypair_request(principal, ?info) &*&
               generated_values(principal, ?count);
  @*/
  /*@ ensures  world(pub) &*&
               generated_values(principal, count + 1) &*&
               keypair(result, principal, count + 1, info);
  @*/
{
  //@ open world(pub);
  
  pk_context *context = malloc(sizeof(struct pk_context));
  if (context == 0) {abort_crypto_lib("Malloc failed");}  
  struct keypair *pair = malloc(sizeof(struct keypair));
  if (pair == 0) {abort_crypto_lib("Malloc failed");}
  
  //@ close pk_context(context);
  pk_init(context);
  if (pk_init_ctx(context, pk_info_from_type(PK_RSA_TYPE)) != 0)
    abort_crypto_lib("Could not generate key_pair: pk_init_ctx failed");
  void *random_state = nonces_expose_state();
  
  //@ open keypair_request(principal, info);
  //@ close rsa_key_request(principal, info);
  /*@ produce_function_pointer_chunk random_function<item>
            (key_item_havege_random_stub)()(state, output, len) { call(); } @*/
  //@ open generated_values(principal, count);
  
  if (rsa_gen_key(context->pk_ctx, key_item_havege_random_stub, 
                  random_state, (unsigned int) RSA_KEY_SIZE, 65537) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: rsa_gen_key failed");
  }
  //@ close generated_values(principal, count + 1);
  nonces_hide_state(random_state);
  retreive_keys(context, &(pair->public_key), &(pair->private_key));
  //@ pk_release_context_with_keys(context);
  pk_free(context);
  //@ open pk_context(context);
  free(context);
  //@ close world(pub);
  
  register_public_key(principal, pair->public_key);
  //@ close keypair(pair, principal, count + 1, info);
  return pair;
}

