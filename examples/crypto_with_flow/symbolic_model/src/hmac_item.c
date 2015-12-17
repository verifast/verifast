#include "hmac_item.h"

#include "key_item.h"
#include "principal_ids.h"
#include "item_constraints.h"
#include "serialization.h"

bool is_hmac(struct item *item)
  //@ requires [?f]world(?pub) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub) &*& item(item, i, pub) &*&
               result ? i == hmac_item(_, _, _) : true; @*/
{
  //@ open [f]world(pub);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_HMAC;
  //@ close item(item, i, pub);
  //@ close [f]world(pub);
}

void check_is_hmac(struct item *item)
  //@ requires [?f]world(?pub) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub) &*& item(item, i, pub) &*&
               i == hmac_item(_, _, _); @*/
{
  if (!is_hmac(item))
    abort_crypto_lib("Presented item is not an hmac");
}

struct item *create_hmac(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
               k == symmetric_key_item(?creator, ?id); @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?hmac, pub) &*&
               col || hmac == hmac_item(creator, id, some(pay)); @*/
{
  //@ open [f]world(pub);
  //@ open item(key, k, pub);
  //@ assert key->content |-> ?k_cont &*& key->size |-> ?k_size;
  check_valid_symmetric_key_item_size(key->size);
  //@ open [_]item_constraints(k, ?k_cs0, pub);
  //@ assert [_]ic_parts(k)(?k_tag, ?k_cs);
  //@ crypto_chars_limits(k_cont);
  //@ crypto_chars_split(k_cont, TAG_LENGTH);
  //@ WELL_FORMED(k_tag, k_cs, TAG_SYMMETRIC_KEY)
  //@ assert crypto_chars(secret, k_cont,TAG_LENGTH, k_tag);
  //@ assert crypto_chars(secret, k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs);
  //@ cryptogram k_cg = cg_symmetric_key(creator, id);
  //@ if (col) k_cg = chars_for_cg_sur(k_cs, tag_symmetric_key);
  //@ if (col) crypto_chars_to_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
  //@ if (col) public_chars_extract(k_cont + TAG_LENGTH, k_cg);
  //@ if (col) chars_to_secret_crypto_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
  //@ close cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);

  //@ open item(payload, pay, pub);
  //@ open [_]item_constraints(pay, ?pay_cs, pub);
  //@ assert payload->content |-> ?p_cont &*& payload->size |-> ?p_size;
  struct item* hmac = malloc(sizeof(struct item));
  if (hmac == 0){abort_crypto_lib("malloc of item failed");}
  hmac->size = TAG_LENGTH + HMAC_SIZE;
  hmac->content = malloc_wrapper(hmac->size);
  write_tag(hmac->content, TAG_HMAC);

  if (payload->size < MINIMAL_STRING_SIZE)
    {abort_crypto_lib("Payload of hmac was to small");}
  sha512_hmac(key->content + TAG_LENGTH, (unsigned int) GCM_KEY_SIZE,
              payload->content, (unsigned int) payload->size,
              hmac->content + TAG_LENGTH, 0);
  //@ assert hmac->content |-> ?cont &*& hmac->size |-> ?size;
  //@ assert chars(cont, TAG_LENGTH, ?cs_tag);
  //@ assert cs_tag == full_tag(TAG_HMAC);
  //@ public_chars(cont, TAG_LENGTH);
  //@ open cryptogram(cont + TAG_LENGTH, HMAC_SIZE, ?h_cs, ?h_cg);
  //@ assert col || h_cg == cg_hmac(creator, id, pay_cs);
  //@ if (col) h_cg == chars_for_cg_sur(h_cs, tag_hmac);
  //@ close exists(h_cg);
  //@ assert h_cg == cg_hmac(?p0, ?c0, _);
  //@ item h = hmac_item(p0, c0, some(pay));
  //@ list<char> cs = append(cs_tag, h_cs);
  //@ chars_to_secret_crypto_chars(cont, TAG_LENGTH);
  //@ crypto_chars_join(cont);
  //@ close [f]world(pub);
  //@ WELL_FORMED(cs_tag, h_cs, TAG_HMAC)
  //@ close ic_parts(h)(cs_tag, h_cs);
  /*@ if (col)
      {
        crypto_chars_to_chars(cont, TAG_LENGTH + HMAC_SIZE);
        public_chars(cont, TAG_LENGTH + HMAC_SIZE);
        chars_to_secret_crypto_chars(cont, TAG_LENGTH + HMAC_SIZE);
        public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
      }
  @*/
  //@ close well_formed_item_chars(h)(pay_cs);
  //@ leak well_formed_item_chars(h)(pay_cs);
  //@ close item_constraints(h, cs, pub);
  //@ leak item_constraints(h, cs, pub);
  //@ close item(hmac, h, pub);

  return hmac;
  //@ open cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);
  //@ crypto_chars_join(k_cont);
  //@ close item(key, k, pub);
  //@ close item(payload, pay, pub);
}

