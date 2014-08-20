#include "hmac_item.h"

#include "item.h"
#include "serialization.h"
#include "principals.h"

struct item *hmac(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*& item(payload, ?p) &*&
               item(key, ?k) &*& k == key_item(?creator, ?id, ?kind, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*& item(payload, p) &*&
               item(key, k) &*& item(result, hmac_item(k, p));
  @*/
{
  char *cs_key;
  char *cs_pay;
  int cs_key_length = item_serialize(&cs_key, key);
  int cs_pay_length = item_serialize(&cs_pay, payload);
  
  //@ open [f]world(pub);
  struct item* hmac = malloc(sizeof(struct item));
  if (hmac == 0){abort_crypto_lib("malloc of item failed");}
  hmac->tag = 4;
  hmac->size = HMAC_SIZE;
  hmac->content = malloc_wrapper(HMAC_SIZE);
  sha512_hmac(cs_key, (unsigned int) cs_key_length, 
              cs_pay, (unsigned int) cs_pay_length, 
              hmac->content, 0);
  free(cs_key);
  free(cs_pay);
  //@ sha512_polarssl_item_to_chars(hmac->content);
  //@ open item(payload, p);
  //@ open item(key, k);
  //@ close item(hmac, hmac_item(k, p));
  return hmac;  
  //@ close item(key, k);
  //@ close item(payload, p);
  //@ close [f]world(pub);
}

void hmac_verify(struct item *hash, struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*& item(hash, ?h) &*& item(payload, ?p) &*&
               item(key, key_item(?creator, ?id, ?kind, ?info)); @*/
  /*@ ensures  [f]world(pub) &*& item(hash, h) &*& item(payload, p) &*&
               item(key, key_item(creator, id, kind, info)) &*&
               collision_in_run() ? 
                   true 
                 : 
                   h == hmac_item(key_item(creator, id, kind, info), p); @*/
{
  struct item *calucated_hash = hmac(key, payload);
  if (!item_equals(hash, calucated_hash))
    abort_crypto_lib("Hash to verify was not correct");
  item_free(calucated_hash);
}

bool is_hmac(struct item *item)
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
            return result == false;
          case hmac_item(k0, pay0):
            return result == true;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/
{
  //@ open item(item, i);
  return (item->tag == 4);
  //@ close item(item, i);
}

void check_is_hmac(struct item *item)
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
          case hmac_item(k0, pay0):
            return item(item, hmac_item(k0, pay0));
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/
{
  if (!is_hmac(item))
    abort_crypto_lib("Presented item is not an hmac");
}
