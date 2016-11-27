#include "key_register.h"

#include "principal_ids.h"

struct key_registry
{
  int participant;
  struct item* pub_key;
  struct key_registry* next;
};

struct key_registry *registered_keys = 0;

/*@

predicate key_registry(struct key_registry *node, predicate(item) pub) =
  node == 0 ?
    true
  :
    node->next |-> ?next &*&
      key_registry(next, pub) &*&
    node->participant |-> ?participant &*&
    node->pub_key |-> ?key &*&
      item(key, public_key_item(participant, 1), pub) &*&
      key != 0 &*&
    malloc_block_key_registry(node)
;

predicate key_registry_initialized(predicate(item) pub) =
  pointer(&registered_keys, ?head) &*&
  key_registry(head, pub)
;

@*/

void key_registry_init()
  /*@ requires exists<predicate(item)>(?pub) &*&
               module(key_register, true); @*/
  //@ ensures  key_registry_initialized(pub);
{
  //@ open_module();
  registered_keys = 0;
  //@ close key_registry(0, pub);
  //@ close key_registry_initialized(pub);
}

void clear_key_registry(struct key_registry* head)
  /*@ requires key_registry(head, _); @*/
  /*@ ensures  emp; @*/
{
  //@ open key_registry(head, _);
  if (head != 0)
  {
    clear_key_registry(head->next);
    item_free(head->pub_key);
    free(head);
  }
}

void key_registry_exit()
  /*@ requires key_registry_initialized(_); @*/
  /*@ ensures  module(key_register, false); @*/
{
  //@ open key_registry_initialized(_);
  clear_key_registry(registered_keys);
  registered_keys = 0;
  //@ close_module();
}

void register_public_key(int participant, struct item *key)
  /*@ requires world(?pub, ?key_clsfy) &*&
               item(key, public_key_item(participant, 1), pub); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               item(key, public_key_item(participant, 1), pub); @*/
{
  struct item* clone = item_clone(key);

  //@ open world(pub, key_clsfy);
  struct key_registry *kr = malloc(sizeof(struct key_registry));
  if (kr == 0) {abort_crypto_lib("malloc failed");}

  //@ open key_registry_initialized(pub);
  kr->participant = participant;
  kr->pub_key = clone;
  kr->next = registered_keys;
  registered_keys = kr;

  //@ assert pointer(&registered_keys, ?head);
  //@ close key_registry(head, pub);
  //@ close key_registry_initialized(pub);
  //@ close world(pub, key_clsfy);
}

struct item *get_public_key(int participant)
  //@ requires [?f]world(?pub, ?key_clsfy);
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(result, public_key_item(participant, 1), pub);
  @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open [f]key_registry_initialized(pub);

  if (participant < 1)
    abort_crypto_lib("Participant does not exist");

  struct item *result = 0;
  struct key_registry* current = registered_keys;
  while(current != 0 && result == 0)
   /*@ requires  [f]key_registry(current, pub) &*&
                 result == 0 ?
                   true
                 :
                   item(result, public_key_item(participant, 1), pub); @*/
   /*@ ensures   [f]key_registry(old_current, pub) &*&
                 result == 0 ?
                   true
                 :
                   item(result, public_key_item(participant, 1), pub); @*/
  {
    //@ open [f]key_registry(current, pub);
    if (current->participant == participant)
    {
      result = item_clone(current->pub_key);
      //@ close [f]key_registry(old_current, pub);
      break;
    }
    current = current->next;

    //@ recursive_call();
    //@ close [f]key_registry(old_current, pub);
  }

  if (result == 0)
    abort_crypto_lib("Participant does not exist");

  return result;
  //@ close [f]key_registry_initialized(pub);
  //@ close [f]world(pub, key_clsfy);
}
