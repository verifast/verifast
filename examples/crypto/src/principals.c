#include "principals.h"

int counter;

/*@
predicate principals_created(int count) = 
  count >= 0 &*&
  integer(&counter, count) &*&
  polarssl_principals(count)
;
@*/

void principals_init()
  /*@ requires [?f]world(?pub) &*&
               polarssl_principals(0) &*&
               module(principals, true); @*/
  /*@ ensures  [f]world(pub) &*& 
               initial_principals(); @*/
{
  //@ open_module();
  counter = 0;
  //@ close principals_created(0);
  //@ close initial_principals();
}

/*@
lemma void principals_exit()
  requires [?f]world(?pub) &*&
           principals_created(?count);
  ensures  [f]world(pub) &*&
           polarssl_principals(_) &*&
           module(principals, false);
{
  open principals_created(count);
  close_module();
}
@*/

int create_principal()
  //@ requires [?f]world(?pub) &*& principals_created(?count);
  /*@ ensures  [f]world(pub) &*& principals_created(count + 1) &*& 
               principal(count + 1) &*& generated_values(count + 1, 0) &*&
               result == count + 1; @*/
{
  //@ open [f]world(pub);
  //@ open principals_created(count);
  //@ create_polarssl_principal(count);
  
  if (counter >= INT_MAX - 1)
  {
    //@ close [f]world(pub);
    abort_crypto_lib("To many principals generated");
  }
    
  counter++;
  return counter;
  
  //@ close principal(count + 1);
  //@ close generated_values(count + 1, 0);
  //@ close principals_created(count + 1);
  //@ close [f]world(pub);
}

/*@

lemma void destroy_principal(int count)
  requires [?f]world(?pub) &*& principal(count) &*&
           generated_values(count, _);
  ensures  [f]world(pub);
{
  open principal(count);
  open generated_values(count, _);
  open [f]world(pub);
  destroy_polarssl_principal(count);
  close [f]world(pub);
}

@*/