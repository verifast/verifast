#include "hash_item.h"

#include "principal_ids.h"
#include "item_constraints.h"
#include "serialization.h"

bool is_hash(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == hash_item(_) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_HASH;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_hash(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  //@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*& i == hash_item(_);
{
  if (!is_hash(item))
    abort_crypto_lib("Presented item is not a hash");
}

struct item *create_hash(struct item *payload)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(payload, ?pay, pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(payload, pay, pub) &*& item(result, ?hash, pub) &*&
               col || hash == hash_item(some(pay)); @*/
{
  //@ open [f1]item(payload, pay, pub);
  //@ open [_]item_constraints(pay, ?pay_ccs, pub);
  //@ item_constraints_memcmp(pay);
  //@ assert [f1]payload->content |-> ?p_cont &*& [f1]payload->size |-> ?p_size;
  struct item* hash = malloc(sizeof(struct item));
  if (hash == 0){abort_crypto_lib("malloc of item failed");}

  hash->size = TAG_LENGTH + HASH_SIZE;
  hash->content = malloc_wrapper(hash->size);
  write_tag(hash->content, TAG_HASH);

  if (payload->size < MINIMAL_STRING_SIZE)
    {abort_crypto_lib("Payload of hash was to small");} //~allow_dead_code
  sha512(payload->content, (unsigned int) payload->size, hash->content + TAG_LENGTH, 0);

  //@ open [f0]world(pub, key_clsfy);
  //@ assert hash->content |-> ?cont &*& hash->size |-> ?size;
  //@ open cryptogram(cont + TAG_LENGTH, HASH_SIZE, ?ccs_cont, ?h_cg);
  //@ item h = hash_item(some(pay));
  //@ close ic_cg(h)(ccs_cont, h_cg);
  //@ close [f0]world(pub, key_clsfy);
  //@ close well_formed_item_ccs(h)(pay_ccs);
  //@ leak well_formed_item_ccs(h)(pay_ccs);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_HASH, size, h)
  //@ close item(hash, h, pub);

  return hash;
  //@ close [f1]item(payload, pay, pub);
}
