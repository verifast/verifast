#include "principal_ids.h"
#include "key_item.h"

//@ import_module principals_mod;

int counter;

/*@
predicate principals_created(int count) =
  count >= 0 &*&
  integer(&counter, count) &*&
  principals(count)
;

predicate principals_created_temp(int* c) =
  c == &counter
;
@*/

void principals_initialize()
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               module(principal_ids, true); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& 
               principals_created(0); @*/
{
  //@ open_module();
  counter = 0;
  //@ principals_init();
  //@ close principals_created(0);
}

/*@
lemma void principals_finalize()
  requires [?f]world(?pub, ?key_clsfy) &*&
           principals_created(?count);
  ensures  [f]world(pub, key_clsfy);
{
  open principals_created(count);
  principals_exit();
  leak integer(&counter, _);
}
@*/

int create_principal(struct keypair** keypair)
  /*@ requires world(?pub, ?key_clsfy) &*&
               *keypair |-> _ &*&
               principals_created(?count); @*/
  /*@ ensures  world(pub, key_clsfy) &*&
               principals_created(result) &*&
               result == count + 1 &*&
               principal(result, 1) &*&
               pointer(keypair, ?p_keypair) &*&
               keypair(p_keypair, result, 1, 0, pub); @*/
{
  //@ open principals_created(count);
  //@ principal_create();
  
  if (counter >= INT_MAX - 1)
  {
    abort_crypto_lib("To many principals generated");
  }
  
  counter++;
  //@ close keypair_request(count + 1, 0);
  struct keypair *k = create_keypair(counter);
  *keypair = k;
  struct item *key = keypair_get_public_key(k);
  register_public_key(counter, key);
  item_free(key);
  
  return counter;
  //@ close principals_created(count + 1);
}

int* get_polarssl_principals()
  //@ requires principals_created(?count);
  /*@ ensures  principals_created_temp(result) &*& integer(result, count) &*&
               principals(count) &*& count >= 0; @*/
{
  //@ open principals_created(count);
  //@ close principals_created_temp(&counter);
  return &counter;
}

/*@
lemma void return_polarssl_principals()
  requires principals_created_temp(?counter) &*& integer(counter, ?count) &*&
           count >= 0 &*& principals(count);
  ensures  principals_created(count);
{
  open principals_created_temp(_);
  close principals_created(count);
}

@*/