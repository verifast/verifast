#include "hash_item.h"

#include "principals.h"
#include "item_constraints.h"
#include "serialization.h"

bool is_hash(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == hash_item(_) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'd';
  //@ close item(item, i, pub);
}

void check_is_hash(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == hash_item(_);
{
  if (!is_hash(item))
    abort_crypto_lib("Presented item is not a hash");
}

struct item *create_hash(struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, pay, pub) &*& item(result, ?hash, pub) &*& 
               collision_in_run() ? 
                 true
               :
                 hash == hash_item(some(pay)); @*/
{
  //@ open item(payload, pay, pub);
  //@ open [_]item_constraints(_, pay, ?pay_cs, pub);
  struct item* hash = malloc(sizeof(struct item));
  if (hash == 0){abort_crypto_lib("malloc of item failed");}
  
  hash->size = 1 + HASH_SIZE;
  hash->content = malloc_wrapper(hash->size);
  *(hash->content) = 'd';
  
  if (payload->size < POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE)
    {abort_crypto_lib("Payload of hash was to small");}
  sha512(payload->content, (unsigned int) payload->size, hash->content + 1, 0);
   
  //@ assert hash->content |-> ?cont &*& hash->size |-> ?size;
  //@ open polarssl_cryptogram(cont + 1, HASH_SIZE, ?h_cs, ?h_cg);
  /*@ if (collision_in_run())
      {
        item h = dummy_item_for_tag('d');
        assert chars(cont, size, ?cs);
        collision_public(pub, cs);
        close item_constraints(true, h, cs, pub);
        leak item_constraints(true, h, cs, pub);
        close item(hash, h, pub);
      }
      else
      {
        item h = hash_item(some(pay));
        list<char> cs = cons('d', h_cs);
        assert chars(cont, size, cs);
        assert h_cg == polarssl_hash(pay_cs);
        item_constraints_well_formed(pay, h);
        close item_constraints_no_collision(h, cs, pub);
        leak item_constraints_no_collision(h, cs, pub);
        close item_constraints(false, h, cs, pub);
        leak item_constraints(false, h, cs, pub);
        close item(hash, h, pub);
      }
  @*/
  
  return hash;
  //@ close item(payload, pay, pub);
}
