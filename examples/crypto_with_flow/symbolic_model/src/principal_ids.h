#ifndef PRINCIPAL_IDS_H
#define PRINCIPAL_IDS_H

#include "general.h"
#include "debug.h"
#include "item.h"
#include "invariants.h"

//@ require_module principal_ids;

//@ predicate principals_created_temp(int* counter);

void principals_initialize();
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               module(principal_ids, true); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& 
               principals_created(0); @*/

/*@
lemma void principals_finalize();
  requires [?f]world(?pub, ?key_clsfy) &*&
           principals_created(?count);
  ensures  [f]world(pub, key_clsfy);
@*/

int* get_polarssl_principals();
  //@ requires principals_created(?count);
  /*@ ensures  principals_created_temp(result) &*& integer(result, count) &*&
               principals(count) &*& count >= 0; @*/

/*@
lemma void return_polarssl_principals();
  requires principals_created_temp(?counter) &*& integer(counter, ?count) &*&
           count >= 0 &*& principals(count);
  ensures  principals_created(count);
@*/

#endif
