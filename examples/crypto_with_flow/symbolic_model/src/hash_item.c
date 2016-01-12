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
  //@ open [_]item_constraints(pay, ?pay_cs, pub);
  //@ assert [f1]payload->content |-> ?p_cont &*& [f1]payload->size |-> ?p_size;
  struct item* hash = malloc(sizeof(struct item));
  if (hash == 0){abort_crypto_lib("malloc of item failed");}
  
  hash->size = TAG_LENGTH + HASH_SIZE;
  hash->content = malloc_wrapper(hash->size);
  write_tag(hash->content, TAG_HASH);
  
  if (payload->size < MINIMAL_STRING_SIZE)
    {abort_crypto_lib("Payload of hash was to small");}
  sha512(payload->content, (unsigned int) payload->size, hash->content + TAG_LENGTH, 0);
  
  //@ open [f0]world(pub, key_clsfy);  
  //@ assert hash->content |-> ?cont &*& hash->size |-> ?size;
  //@ public_chars(cont, TAG_LENGTH);
  //@ assert chars(cont, TAG_LENGTH, ?cs_tag);
  //@ assert cs_tag == full_tag(TAG_HASH);
  //@ open cryptogram(cont + TAG_LENGTH, HASH_SIZE, ?cs_cont, ?h_cg);
  //@ assert h_cg == cg_hash(pay_cs);
  //@ close exists(h_cg);
  //@ item h = hash_item(some(pay));
  //@ list<char> cs = append(cs_tag, cs_cont);
  //@ if (col) public_chars(cont + TAG_LENGTH, HASH_SIZE);
  //@ if (col) public_generated_join(polarssl_pub(pub), cs_tag, cs_cont);  
  //@ if (col) chars_to_secret_crypto_chars(cont + TAG_LENGTH, HASH_SIZE);
  //@ chars_to_secret_crypto_chars(cont, TAG_LENGTH);
  //@ crypto_chars_join(cont);
  //@ close [f0]world(pub, key_clsfy);
  //@ close ic_parts(h)(cs_tag, cs_cont);
  //@ WELL_FORMED(cs_tag, cs_cont, TAG_HASH)
  //@ close well_formed_item_chars(h)(pay_cs);
  //@ leak well_formed_item_chars(h)(pay_cs);
  //@ close item_constraints(h, cs, pub);
  //@ leak item_constraints(h, cs, pub);
  //@ close item(hash, h, pub);
  
  return hash;
  //@ close [f1]item(payload, pay, pub);
}
