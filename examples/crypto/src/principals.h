#ifndef PRINCIPALS_H
#define PRINCIPALS_H

#include "general.h"
#include "debug.h"
#include "item.h"
#include "nonce_item.h"
#include "key_item.h"
#include "polarssl_invariants.h"

// see ../include/cryptolib.h

//@ require_module principals;

/*@ 

predicate world(fixpoint(item, bool) pub) =
  debug_initialized() &*&
  nonces_initialized() &*&
  key_registry_initialized() &*&
  polarssl_world<item>(polarssl_pub(pub))
;

predicate principal(int p) =
  polarssl_principal(p)
;

predicate generated_values(int principal, int count) =
  polarssl_generated_values(principal, count)
;

@*/

void principals_init();
  /*@ requires [?f]world(?pub) &*&
               polarssl_principals(0) &*&
               module(principals, true); @*/
  /*@ ensures  [f]world(pub) &*& 
               initial_principals(); @*/

/*@
lemma void principals_exit();
  requires [?f]world(?pub) &*&
           principals_created(?count);
  ensures  [f]world(pub) &*&
           polarssl_principals(_) &*&
           module(principals, false);
@*/
#endif
