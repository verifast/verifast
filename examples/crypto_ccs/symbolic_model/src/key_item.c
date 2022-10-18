#include "key_item.h"

#include "principal_ids.h"

#include "limits.h"

//Symmetric keys

bool is_symmetric_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == symmetric_key_item(_, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_SYMMETRIC_KEY;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_symmetric_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == symmetric_key_item(_, _); @*/
{
  if (!is_symmetric_key(item))
    abort_crypto_lib("Presented item is not a symmetric key");
}

void check_valid_symmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == TAG_LENGTH + GCM_KEY_SIZE;
{
  if (size != TAG_LENGTH + GCM_KEY_SIZE)
    abort_crypto_lib("Illegal size for symmetric key item");
}

struct item *create_symmetric_key()
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               key_request(?principal, ?info) &*&
               principal(principal, ?count); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               principal(principal, count + 1) &*&
               item(result, ?k, pub) &*&
               k == symmetric_key_item(principal, count + 1) &*&
               info_for_item(k) == info; @*/
{
  struct item* key = malloc(sizeof(struct item));
  if (key == 0){abort_crypto_lib("malloc of item failed");}
  key->size = TAG_LENGTH + GCM_KEY_SIZE;
  key->content = malloc_wrapper(key->size);
  write_tag(key->content, TAG_SYMMETRIC_KEY);

  //@ open [f0]world(pub, key_clsfy);
  //@ open key_request(principal, info);
  //@ close random_request(principal, info, true);
  void* state = nonces_expose_state();
  //@ open principal(principal, count);
  if (havege_random((void*) state, key->content + TAG_LENGTH, GCM_KEY_SIZE) != 0)
    abort_crypto_lib("Generation of random value failed");
  nonces_hide_state(state);
  //@ close principal(principal, count + 1);

  //@ item k = symmetric_key_item(principal, count + 1);
  //@ assert key->content |-> ?cont &*& key->size |-> ?size;
  //@ open cryptogram(cont + TAG_LENGTH, GCM_KEY_SIZE, ?ccs_cont, ?k_cg);
  //@ assert k_cg == cg_symmetric_key(principal, count + 1);
  //@ close ic_cg(k)(ccs_cont, k_cg);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_SYMMETRIC_KEY, size, k)
  //@ close item(key, k, pub);
  //@ close [f0]world(pub, key_clsfy);
  return key;
}

//Asymmetric keys

bool is_public_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == public_key_item(_, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_PUBLIC_KEY;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_public_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == public_key_item(_, _); @*/
{
  if (!is_public_key(item))
    abort_crypto_lib("Presented item is not a public key");
}

bool is_private_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == private_key_item(_, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_PRIVATE_KEY;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_private_key(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == private_key_item(_, _); @*/
{
  if (!is_private_key(item))
    abort_crypto_lib("Presented item is not a private key");
}

void check_valid_asymmetric_key_item_size(int size)
  //@ requires true;
  //@ ensures  size == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE;
{
  if (size != TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE)
    abort_crypto_lib("Illegal size for asymmetric key item");
}

int key_item_havege_random_stub(void *havege_state,
                                char *output, size_t len)
  /*@ requires [?f]havege_state_initialized(havege_state) &*&
               random_request(?principal, ?info, ?key_request) &*&
               random_permission(principal, ?count) &*&
               chars_(output, len, _) &*& len >= MIN_RANDOM_SIZE;
  @*/
  /*@ ensures  [f]havege_state_initialized(havege_state) &*&
               random_permission(principal, count + 1) &*&
               result == 0 ?
                 cryptogram(output, len, ?cs, ?cg) &*&
                 info == cg_info(cg) &*&
                 key_request ?
                   cg == cg_symmetric_key(principal, count + 1)
                 :
                   cg == cg_nonce(principal, count + 1)
               :
                 chars_(output, len, _);
  @*/
{
  return havege_random(havege_state, output, len);
}

void retreive_keys(pk_context *ctx, struct item **public, struct item **private)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               pk_context_with_keys(ctx, ?principal, ?count, RSA_BIT_KEY_SIZE, ?info) &*&
               pointer_(public, _) &*& pointer_(private, _); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               pk_context_with_keys(ctx, principal, count, RSA_BIT_KEY_SIZE, info) &*&
               pointer(public, ?pub_key) &*& pointer(private, ?priv_key) &*&
               item(pub_key, ?pub_key_i, pub) &*&
                 pub_key_i == public_key_item(principal, count) &*&
                 info_for_item(pub_key_i) == info &*&
               item(priv_key, ?priv_key_i, pub) &*&
                 priv_key_i == private_key_item(principal, count) &*&
                 info_for_item(priv_key_i) == info; @*/
{
  struct item* pub_i = malloc(sizeof(struct item));
  struct item* priv_i = malloc(sizeof(struct item));
  if (pub_i == 0 || priv_i == 0) {abort_crypto_lib("Malloc failed");}

  int size = TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE;
  pub_i->size = size;
  pub_i->content = malloc((size_t)pub_i->size);
  if (pub_i->content == 0) {abort_crypto_lib("Malloc failed");}
  priv_i->size = size;
  priv_i->content = malloc((size_t)priv_i->size);
  if (priv_i->content == 0) {abort_crypto_lib("Malloc failed");}

  write_tag(pub_i->content, TAG_PUBLIC_KEY);
  write_tag(priv_i->content, TAG_PRIVATE_KEY);

  if (pk_write_pubkey_pem(ctx, pub_i->content + TAG_LENGTH,
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_pubkey_pem");
  }
  if (pk_write_key_pem(ctx, priv_i->content + TAG_LENGTH,
      (unsigned int) ((int) RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: pk_write_key_pem");
  }

  //@ open [f]world(pub, key_clsfy);
  //@ item key_pub_i = public_key_item(principal, count);
  //@ item key_priv_i = private_key_item(principal, count);
  //@ assert pub_i->content |-> ?cont_pub &*& pub_i->size |-> ?size_pub;
  //@ assert priv_i->content |-> ?cont_priv &*& priv_i->size |-> ?size_priv;
  //@ open cryptogram(cont_pub + TAG_LENGTH, RSA_SERIALIZED_KEY_SIZE, ?cs_pub, ?cg_pub);
  //@ open cryptogram(cont_priv + TAG_LENGTH, RSA_SERIALIZED_KEY_SIZE, ?cs_priv, ?cg_priv);
  //@ close ic_cg(key_pub_i)(cs_pub, cg_pub);
  //@ close ic_cg(key_priv_i)(cs_priv, cg_priv);
  //@ CLOSE_ITEM_CONSTRAINTS(cont_pub, TAG_PUBLIC_KEY, size, key_pub_i)
  //@ CLOSE_ITEM_CONSTRAINTS(cont_priv, TAG_PRIVATE_KEY, size, key_priv_i)
  //@ close item(pub_i, key_pub_i, pub);
  //@ close item(priv_i, key_priv_i, pub);
  //@ close [f]world(pub, key_clsfy);

  *public = pub_i;
  *private = priv_i;
}

void set_public_key(pk_context *ctx, struct item *pub_key)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               pk_context_initialized(ctx) &*&
               item(pub_key, public_key_item(?principal, ?count), pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               pk_context_with_key(ctx, pk_public, ?p1, ?c1, RSA_BIT_KEY_SIZE) &*&
               item(pub_key, public_key_item(principal, count), pub) &*&
               col || p1 == principal && c1 == count; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ item pub_key_i = public_key_item(principal, count);
  //@ open item(pub_key, pub_key_i, pub);
  //@ assert pub_key->size |-> ?size &*& pub_key->content |-> ?cont;
  check_valid_asymmetric_key_item_size(pub_key->size);
  //@ assert [_]item_constraints(pub_key_i, ?ccs, pub);
  //@ OPEN_ITEM_CONSTRAINTS(pub_key_i, ccs, pub)
  //@ assert [_]ic_parts(pub_key_i)(?ccs_tag, ?ccs_cont);
  //@ crypto_chars_split(cont, TAG_LENGTH);
  //@ cryptogram cg = cg_rsa_public_key(principal, count);
  //@ if (col) cg = ccs_for_cg_sur(ccs_cont, tag_public_key);
  //@ if (col) public_ccs_cg(cg);
  //@ close cryptogram(cont + TAG_LENGTH, RSA_BIT_KEY_SIZE, ccs_cont, cg);
  if (pk_parse_public_key(ctx, (void*) pub_key->content + TAG_LENGTH,
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE)) != 0)
  {
    abort_crypto_lib("Could not set public key context");
  }
  //@ open cryptogram(cont + TAG_LENGTH, RSA_BIT_KEY_SIZE, ccs_cont, cg);
  //@ crypto_chars_join(cont);
  //@ close item(pub_key, pub_key_i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void set_private_key(pk_context *ctx, struct item *priv_key)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               pk_context_initialized(ctx) &*&
               item(priv_key, private_key_item(?principal, ?count), pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               pk_context_with_key(ctx, pk_private, ?p1, ?c1, RSA_BIT_KEY_SIZE) &*&
               item(priv_key, private_key_item(principal, count), pub) &*&
               col || p1 == principal && c1 == count; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ item priv_key_i = private_key_item(principal, count);
  //@ open item(priv_key, priv_key_i, pub);
  //@ assert priv_key->size |-> ?size &*& priv_key->content |-> ?cont;
  check_valid_asymmetric_key_item_size(priv_key->size);
  //@ assert [_]item_constraints(priv_key_i, ?ccs, pub);
  //@ OPEN_ITEM_CONSTRAINTS(priv_key_i, ccs, pub)
  //@ assert [_]ic_parts(priv_key_i)(?ccs_tag, ?ccs_cont);
  //@ crypto_chars_split(cont, TAG_LENGTH);
  //@ cryptogram cg = cg_rsa_private_key(principal, count);
  //@ if (col) cg = ccs_for_cg_sur(ccs_cont, tag_private_key);
  //@ if (col) public_ccs_cg(cg);
  //@ close cryptogram(cont + TAG_LENGTH, RSA_BIT_KEY_SIZE, ccs_cont, cg);
  if (pk_parse_key(ctx, (void*) priv_key->content + TAG_LENGTH,
      (unsigned int) (RSA_SERIALIZED_KEY_SIZE), NULL, 0) != 0)
  {
    abort_crypto_lib("Could not set private key context");
  }
  //@ open cryptogram(cont + TAG_LENGTH, RSA_BIT_KEY_SIZE, ccs_cont, cg);
  //@ crypto_chars_join(cont);
  //@ close item(priv_key, priv_key_i, pub);
  //@ close [f]world(pub, key_clsfy);
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
               info_for_item(key) == info; @*/
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
               info_for_item(key) == info; @*/
{
  //@ open keypair(keypair, creator, id, info, pub);
  struct item *key_pub = item_clone(keypair->public_key);
  //@ close keypair(keypair, creator, id, info, pub);

  return key_pub;
}

struct keypair *create_keypair(int principal)
  /*@ requires world(?pub, ?key_clsfy) &*&
               keypair_request(principal, ?info) &*&
               principal(principal, ?count); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               keypair(result, principal, count + 1, info, pub) &*&
               principal(principal, count + 1); @*/
{
  //@ open world(pub, key_clsfy);
  pk_context context;

  struct keypair *pair = malloc(sizeof(struct keypair));
  if (pair == 0) {abort_crypto_lib("Malloc failed");}

  //@ close pk_context(&context);
  pk_init(&context);
  if (pk_init_ctx(&context, pk_info_from_type(MBEDTLS_PK_RSA)) != 0)
    abort_crypto_lib("Could not generate key_pair: pk_init_ctx failed");
  void *random_state = nonces_expose_state();

  //@ open keypair_request(principal, info);
  //@ close rsa_key_request(principal, info);
  /*@ produce_function_pointer_chunk random_function(
                      key_item_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ open principal(principal, count);
  if (rsa_gen_key(context.pk_ctx, key_item_havege_random_stub,
                  random_state, (unsigned int) RSA_BIT_KEY_SIZE, 65537) != 0)
  {
    abort_crypto_lib("Could not generate key_pair: rsa_gen_key failed");
  }
  //@ close principal(principal, count + 1);
  nonces_hide_state(random_state);
  //@ close world(pub, key_clsfy);
  retreive_keys(&context, &(pair->public_key), &(pair->private_key));
  //@ pk_release_context_with_keys(&context);
  pk_free(&context);
  //@ open pk_context(&context);
  //@ close keypair(pair, principal, count + 1, info, pub);
  return pair;
}

/*@
lemma void info_for_asymmetric_keypair(item pub_key, item priv_key)
  requires pub_key == public_key_item(?p, ?c) &*&
           priv_key == private_key_item(p, c);
  ensures  info_for_item(pub_key) == info_for_item(priv_key);
{
  pk_info_for_keypair(p, c);
}
@*/

