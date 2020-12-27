#include "hmac_item.h"

#include "hash_item.h"
#include "key_item.h"
#include "principal_ids.h"
#include "item_constraints.h"
#include "serialization.h"

bool is_hmac(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == hmac_item(_, _, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_HMAC;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_hmac(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == hmac_item(_, _, _); @*/
{
  if (!is_hmac(item))
    abort_crypto_lib("Presented item is not an hmac");
}

struct item *create_hmac(struct item *key, struct item *payload)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(payload, ?pay, pub) &*&
               [?f2]item(key, ?k, pub) &*&
                 k == symmetric_key_item(?creator, ?id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(payload, pay, pub) &*& [f2]item(key, k, pub) &*&
               item(result, ?hmac, pub) &*&
               col || hmac == hmac_item(creator, id, some(pay)); @*/
{
  //@ open [f0]world(pub, key_clsfy);
  //@ open [f2]item(key, k, pub);
  //@ assert [f2]key->content |-> ?k_cont &*& [f2]key->size |-> ?k_size;
  check_valid_symmetric_key_item_size(key->size);
  //@ assert [_]item_constraints(k, ?k_ccs0, pub);
  //@ OPEN_ITEM_CONSTRAINTS(k, k_ccs0, pub)
  //@ assert [_]ic_parts(k)(?k_tag, ?k_ccs);
  //@ crypto_chars_limits(k_cont);
  //@ crypto_chars_split(k_cont, TAG_LENGTH);
  //@ assert [f2]crypto_chars(secret, k_cont, TAG_LENGTH, k_tag);
  //@ assert [f2]crypto_chars(secret, k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_ccs);
  //@ cryptogram k_cg = cg_symmetric_key(creator, id);
  //@ if (col) k_cg = ccs_for_cg_sur(k_ccs, tag_symmetric_key);
  //@ if (col) public_ccs_cg(k_cg);
  //@ close [f2]cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_ccs, k_cg);

  //@ open [f1]item(payload, pay, pub);
  //@ open [_]item_constraints(pay, ?pay_ccs, pub);
  //@ assert [f1]payload->content |-> ?p_cont &*& [f1]payload->size |-> ?p_size;
  struct item* hmac = malloc(sizeof(struct item));
  if (hmac == 0){abort_crypto_lib("malloc of item failed");}
  hmac->size = TAG_LENGTH + HMAC_SIZE;
  hmac->content = malloc_wrapper(hmac->size);
  write_tag(hmac->content, TAG_HMAC);

  if (payload->size < MINIMAL_STRING_SIZE)
    {abort_crypto_lib("Payload of hmac was to small");} //~allow_dead_code
  //@ close [f0]world(pub, key_clsfy);
  //@ item_constraints_memcmp(pay);
  sha512_hmac(key->content + TAG_LENGTH, (unsigned int) GCM_KEY_SIZE,
              payload->content, (unsigned int) payload->size,
              hmac->content + TAG_LENGTH, 0);
  //@ assert hmac->content |-> ?cont &*& hmac->size |-> ?size;
  //@ open cryptogram(cont + TAG_LENGTH, HMAC_SIZE, ?h_ccs, ?h_cg);
  //@ assert col || h_cg == cg_sha512_hmac(creator, id, pay_ccs);
  //@ if (col) h_cg == ccs_for_cg_sur(h_ccs, tag_hmac);
  //@ assert h_cg == cg_sha512_hmac(?p0, ?c0, _);
  //@ item h = hmac_item(p0, c0, some(pay));
  //@ close ic_cg(h)(h_ccs, h_cg);
  //@ close well_formed_item_ccs(h)(pay_ccs);
  //@ leak well_formed_item_ccs(h)(pay_ccs);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_HMAC, size, h)
  //@ close item(hmac, h, pub);

  return hmac;
  //@ open cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_ccs, k_cg);
  //@ crypto_chars_join(k_cont);
  //@ close [f2]item(key, k, pub);
  //@ close [f1]item(payload, pay, pub);
}
