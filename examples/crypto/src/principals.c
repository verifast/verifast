#include "principals.h"
#include "key_item.h"

int counter;

/*@
predicate principals_created(int count) =
  count >= 0 &*&
  integer(&counter, count) &*&
  polarssl_principals(count)
;

predicate principals_created_temp(int* c) =
  c == &counter
;
@*/

void principals_init()
  /*@ requires polarssl_principals(0) &*&
               module(principals, true); @*/
  //@ ensures  principals_created(0);
{
  //@ open_module();
  counter = 0;
  //@ close principals_created(0);
}

/*@
lemma void principals_exit()
  requires principals_created(?count);
  ensures  polarssl_principals(_) &*&
           module(principals, false);
{
  open principals_created(count);
  close_module();
}
@*/

int create_principal(struct keypair **keypair)
  /*@ requires world(?pub) &*&
               pointer(keypair, _) &*&
               principals_created(?count); @*/
  /*@ ensures  world(pub) &*&
               principals_created(result) &*& 
               result == count + 1 &*&
               principal(result) &*& generated_values(result, 1) &*&
               pointer(keypair, ?p_keypair) &*&
               keypair(p_keypair, result, 1, 0, pub); @*/
{
  //@ open principals_created(count);
  //@ polarssl_create_principal();
  
  if (counter >= INT_MAX - 1)
  {
    abort_crypto_lib("To many principals generated");
  }
  
  counter++;
  //@ close principal(count + 1);
  //@ close generated_values(count + 1, 0);
  //@ close keypair_request(count + 1, 0);
  struct keypair *k = create_keypair(counter);
  *keypair = k;
  struct item *key = keypair_get_public_key(k);
  register_public_key(counter, key);
  item_free(key);
  
  return counter;
  //@ close principals_created(count + 1);
}

/*@

lemma void destroy_principal(int count)
  requires principal(count) &*&
           generated_values(count, _);
  ensures  emp;
{
  open principal(count);
  open generated_values(count, _);
  polarssl_destroy_principal(count);
}

@*/

int* get_polarssl_principals()
  //@ requires principals_created(?count);
  /*@ ensures  principals_created_temp(result) &*& integer(result, count) &*&
               polarssl_principals(count) &*& count >= 0; @*/
{
  //@ open principals_created(count);
  //@ close principals_created_temp(&counter);
  return &counter;
}

/*@
lemma void return_polarssl_principals()
  requires principals_created_temp(?counter) &*& integer(counter, ?count) &*&
           count >= 0 &*& polarssl_principals(count);
  ensures  principals_created(count);
{
  open principals_created_temp(_);
  close principals_created(count);
}

@*/