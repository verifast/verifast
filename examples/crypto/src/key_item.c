#include "key_item.h"

#include "principals.h"
#include "item_constraints.h"

#include "limits.h"

//Symmetric keys

bool is_symmetric_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == symmetric_key_item(_, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'e';
  //@ close item(item, i, pub);
}

void check_is_symmetric_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == symmetric_key_item(_, _);
{
  if (!is_symmetric_key(item))
    abort_crypto_lib("Presented item is not a symmetric key");
}

void check_valid_symmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == 1 + GCM_KEY_SIZE;
{
  if (size != 1 + GCM_KEY_SIZE)
    abort_crypto_lib("Illegal size for symmetric key item");
}

struct item *create_symmetric_key()
  /*@ requires [?f0]world(?pub) &*&
               key_request(?principal, ?info) &*&
               generated_values(principal, ?count); @*/
  /*@ ensures  [f0]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?k, pub) &*&
               k == symmetric_key_item(principal, count + 1) &*&
               [_]info_for_item(k, info); @*/
{
  struct item* key = malloc(sizeof(struct item));
  if (key == 0){abort_crypto_lib("malloc of item failed");}
  key->size = 1 + GCM_KEY_SIZE;
  key->content = malloc_wrapper(key->size);
  *(key->content) = 'e';
  
  //@ open [f0]world(pub);
  //@ open key_request(principal, info);
  //@ close random_request(principal, info, true);
  //@ open generated_values(principal, count);
  void* state = nonces_expose_state();
  if (havege_random((void*) state, key->content + 1, GCM_KEY_SIZE) != 0)
    abort_crypto_lib("Generation of random value failed");
  nonces_hide_state(state);
  //@ close generated_values(principal, count + 1);
  
  //@ item key_i = symmetric_key_item(principal, count + 1);
  //@ assert key->content |-> ?cont;
  //@ open polarssl_cryptogram(cont + 1, GCM_KEY_SIZE, ?k_cs, ?k_cg);
  //@ close exists(pair(principal, count + 1));
  //@ close item_constraints_no_collision(key_i, cons('e', k_cs), pub);
  //@ leak item_constraints_no_collision(key_i, cons('e', k_cs), pub);
  //@ close item_constraints(false, key_i, cons('e', k_cs), pub);
  //@ leak item_constraints(false, key_i, cons('e', k_cs), pub);
  //@ close item(key, key_i, pub);
  //@ close info_for_item(key_i, info);
  //@ leak info_for_item(key_i, info);
  //@ close [f0]world(pub);
  return key;
} 

//Asymmetric keys

bool is_public_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == public_key_item(_, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'f';
  //@ close item(item, i, pub);
}

void check_is_public_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == public_key_item(_, _);
{
  if (!is_public_key(item))
    abort_crypto_lib("Presented item is not a public key");
}

bool is_private_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == private_key_item(_, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'g';
  //@ close item(item, i, pub);
}

void check_is_private_key(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == private_key_item(_, _);
{
  if (!is_private_key(item))
    abort_crypto_lib("Presented item is not a private key");
}

void check_valid_asymmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == 1 + RSA_SERIALIZED_KEY_SIZE;
{
  if (size != 1 + RSA_SERIALIZED_KEY_SIZE)
    abort_crypto_lib("Illegal size for asymmetric key item");
}

int key_item_havege_random_stub(void *havege_state, 
                                char *output, size_t len)
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
{
  return havege_random(havege_state, output, len);
}

void retreive_keys(pk_context *ctx, struct item **public, struct item **private)
  /*@ requires world(?pub) &*&
               pk_context_with_keys(ctx, ?principal, ?count, RSA_BIT_KEY_SIZE, ?info) &*&
               pointer(public, _) &*& pointer(private, _); @*/
  /*@ ensures  world(pub) &*&
               pk_context_with_keys(ctx, principal, count, RSA_BIT_KEY_SIZE, info) &*&
               pointer(public, ?pub_key) &*& pointer(private, ?priv_key) &*&
               item(pub_key, ?pub_key_i, pub) &*& 
                 pub_key_i == public_key_item(principal, count) &*&
                 [_]info_for_item(pub_key_i, info) &*&
               item(priv_key, ?priv_key_i, pub) &*&
                 priv_key_i == private_key_item(principal, count) &*&
                 [_]info_for_item(priv_key_i, info); @*/
{
  struct item* pub_i = malloc(sizeof(struct item));
  struct item* priv_i = malloc(sizeof(struct item));
  if (pub_i == 0 || priv_i == 0) {abort_crypto_lib("Malloc failed");}

  pub_i->size = 1 + RSA_SERIALIZED_KEY_SIZE;
  pub_i->content = malloc(pub_i->size);
  if (pub_i->content == 0) {abort_crypto_lib("Malloc failed");}
  priv_i->size = 1 + RSA_SERIALIZED_KEY_SIZE;;
  priv_i->content = malloc(priv_i->size);
  if (priv_i->content == 0) {abort_crypto_lib("Malloc failed");} 

  *(pub_i->content)  = 'f';
  *(priv_i->content) = 'g';
  
  if (pk_write_pubkey_pem(ctx, pub_i->content + 1, 
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_pubkey_pem");
  }
  if (pk_write_key_pem(ctx, priv_i->content + 1, 
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_key_pem");
  }
  
  //@ item key_pub_i = public_key_item(principal, count);
  //@ item key_priv_i = private_key_item(principal, count);
  //@ assert pub_i->content |-> ?cont_pub;
  //@ assert priv_i->content |-> ?cont_priv;
  /*@ open polarssl_cryptogram(cont_pub + 1, RSA_SERIALIZED_KEY_SIZE, 
                               ?pub_cs, ?pub_cg); @*/
  /*@ open polarssl_cryptogram(cont_priv + 1, RSA_SERIALIZED_KEY_SIZE, 
                               ?priv_cs, ?priv_cg); @*/
  //@ close exists(pair(principal, count));
  //@ close item_constraints_no_collision(key_pub_i, cons('f', pub_cs), pub);
  //@ leak item_constraints_no_collision(key_pub_i, cons('f', pub_cs), pub);
  //@ close item_constraints(false, key_pub_i, cons('f', pub_cs), pub);
  //@ leak item_constraints(false, key_pub_i, cons('f', pub_cs), pub);  
  //@ close exists(pair(principal, count));
  //@ close item_constraints_no_collision(key_priv_i, cons('g', priv_cs), pub);
  //@ leak item_constraints_no_collision(key_priv_i, cons('g', priv_cs), pub);
  //@ close item_constraints(false, key_priv_i, cons('g', priv_cs), pub);
  //@ leak item_constraints(false, key_priv_i, cons('g', priv_cs), pub);
  
  //@ close item(pub_i, key_pub_i, pub);
  //@ close item(priv_i, key_priv_i, pub);
  //@ close info_for_item(key_pub_i, info);
  //@ leak info_for_item(key_pub_i, info);
  //@ close info_for_item(key_priv_i, info);
  //@ leak info_for_item(key_priv_i, info);
  
  *public = pub_i;
  *private = priv_i;
}

void set_public_key(pk_context *ctx, struct item *pub_key)
  /*@ requires pk_context_initialized(ctx) &*&
               item(pub_key, public_key_item(?principal, ?count), ?pub); @*/
  /*@ ensures  item(pub_key, public_key_item(principal, count), pub) &*&
               pk_context_with_key(ctx, pk_public, RSA_BIT_KEY_SIZE, ?id) &*&
               collision_in_run() ? 
                 true 
               : 
                 id == some(pair(principal, count)); @*/
{
  //@ item pub_key_i = public_key_item(principal, count);
  //@ open item(pub_key, pub_key_i, pub);
  check_valid_asymmetric_key_item_size(pub_key->size);
  
  //@ assert pub_key->content |-> ?cont;
  //@ chars_limits(pub_key->content);
  //@ chars_split(pub_key->content, 1);
  //@ close polarssl_key_id(principal, count);
  if (pk_parse_public_key(ctx, (void*) pub_key->content + 1, 
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not set public key context");
  }
  //@ open [_]item_constraints(?b, pub_key_i, _, _);
  //@ if (!b) open [_]item_constraints_no_collision(pub_key_i, _, pub);
  //@ close item(pub_key, pub_key_i, pub);
}

void set_private_key(pk_context *ctx, struct item *priv_key)
  /*@ requires pk_context_initialized(ctx) &*&
               item(priv_key, private_key_item(?principal, ?count), ?pub); @*/
  /*@ ensures  item(priv_key, private_key_item(principal, count), pub) &*&
               pk_context_with_key(ctx, pk_private, RSA_BIT_KEY_SIZE, ?id) &*&
               collision_in_run() ? 
                 true 
               : 
                 id == some(pair(principal, count)); @*/
{
  //@ item priv_key_i = private_key_item(principal, count);
  //@ open item(priv_key, priv_key_i, pub);
  check_valid_asymmetric_key_item_size(priv_key->size);
  
  //@ assert priv_key->content |-> ?cont;
  //@ chars_limits(priv_key->content);
  //@ chars_split(priv_key->content, 1);
  //@ close polarssl_key_id(principal, count);
  if (pk_parse_key(ctx, (void*) priv_key->content + 1,
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE), NULL, 0) != 0)
  {
    abort_crypto_lib("Could not set private key context");
  }
  //@ open [_]item_constraints(?b, priv_key_i, _, _);
  //@ if (!b) open [_]item_constraints_no_collision(priv_key_i, _, pub);
  //@ close item(priv_key, priv_key_i, pub);
}

void keypair_free(struct keypair *keypair)
  //@ requires keypair(keypair, ?principal, ?count, ?info, ?pub);
  //@ ensures  true;
{
  //@ open keypair(keypair, _, _, _, _);
  item_free(keypair->private_key);
  item_free(keypair->public_key);
  free(keypair);
}

struct item *keypair_get_private_key(struct keypair *keypair)
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == private_key_item(creator, id) &*&
               [_]info_for_item(key, info); @*/
{
  //@ open keypair(keypair, creator, id, info, pub);
  return item_clone(keypair->private_key);
  //@ close keypair(keypair, creator, id, info, pub);
}

struct item *keypair_get_public_key(struct keypair *keypair)
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == public_key_item(creator, id) &*&
               [_]info_for_item(key, info); @*/
{
  //@ open keypair(keypair, creator, id, info, pub);
  struct item *key_pub = item_clone(keypair->public_key);
  //@ close keypair(keypair, creator, id, info, pub);

  return key_pub;
}



struct keypair *create_keypair(int principal)
  /*@ requires world(?pub) &*&
               keypair_request(principal, ?info) &*&
               generated_values(principal, ?count); @*/
  /*@ ensures  world(pub) &*&
               keypair(result, principal, count + 1, info, pub) &*&
               generated_values(principal, count + 1); @*/
{
  //@ open world(pub);
  pk_context context;
  
  struct keypair *pair = malloc(sizeof(struct keypair));
  if (pair == 0) {abort_crypto_lib("Malloc failed");}
  
  //@ close pk_context(&context);
  pk_init(&context);
  if (pk_init_ctx(&context, pk_info_from_type(POLARSSL_PK_RSA_TYPE)) != 0)
    abort_crypto_lib("Could not generate key_pair: pk_init_ctx failed");
  void *random_state = nonces_expose_state();
  
  //@ open keypair_request(principal, info);
  //@ close rsa_key_request(principal, info);
  //@ open generated_values(principal, count);
  //@ close random_function_predicate(havege_state_initialized);
  /*@ produce_function_pointer_chunk random_function(
                      key_item_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
  if (rsa_gen_key(context.pk_ctx, key_item_havege_random_stub, 
                  random_state, (unsigned int) RSA_BIT_KEY_SIZE, 65537) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: rsa_gen_key failed");
  }
  //@ close generated_values(principal, count + 1);
  nonces_hide_state(random_state);
  //@ close world(pub);
  retreive_keys(&context, &(pair->public_key), &(pair->private_key));
  //@ pk_release_context_with_keys(&context);
  pk_free(&context);
  //@ open pk_context(&context);
  //@ close keypair(pair, principal, count + 1, info, pub);
  return pair;
}

/*@
lemma void info_for_asymmetric_keypair(item pub_key, item priv_key)
  requires [_]info_for_item(pub_key, ?info1) &*&
           pub_key == public_key_item(?p, ?c) &*&
           [_]info_for_item(priv_key, ?info2) &*&
           priv_key == private_key_item(p, c);
  ensures  info1 == info2;
{
  open [_]info_for_item(pub_key, info1);
  open [_]info_for_item(priv_key, info2);
  polarssl_info_for_keypair(p, c);
}
@*/

