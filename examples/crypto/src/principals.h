#ifndef PRINCIPALS_H
#define PRINCIPALS_H

#include "general.h"
#include "debug.h"
#include "item.h"
#include "invariants.h"

//@ require_module principals;

/*@ 

predicate principal(int p) =
  polarssl_principal(p)
;

predicate generated_values(int principal, int count) =
  polarssl_generated_values(principal, count)
;

predicate principals_created_temp(int* counter);

@*/

void principals_init();
  /*@ requires [?f]world(?pub) &*&
               polarssl_principals(0) &*&
               module(principals, true); @*/
  /*@ ensures  [f]world(pub) &*& 
               principals_created(0); @*/

/*@
lemma void principals_exit();
  requires [?f]world(?pub) &*&
           principals_created(?count);
  ensures  [f]world(pub) &*&
           polarssl_principals(_) &*&
           module(principals, false);
@*/

int* get_polarssl_principals();
  //@ requires principals_created(?count);
  /*@ ensures  principals_created_temp(result) &*& integer(result, count) &*&
               polarssl_principals(count) &*& count >= 0; @*/

/*@
lemma void return_polarssl_principals();
  requires principals_created_temp(?counter) &*& integer(counter, ?count) &*&
           count >= 0 &*& polarssl_principals(count);
  ensures  principals_created(count);
@*/

#endif
