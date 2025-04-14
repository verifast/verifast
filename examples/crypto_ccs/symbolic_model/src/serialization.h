#ifndef SERIALIZATION_H
#define SERIALIZATION_H

#include "invariants.h"
#include "general.h"
#include "item_constraints.h"

/*@
  
lemma void serialize_item(item i);
  requires proof_obligations(?pub) &*&
           [_]public_invar(polarssl_pub(pub)) &*&
           [_]item_constraints(i, ?ccs, pub) &*&
           [_]pub(i);
  ensures  proof_obligations(pub) &*& 
           [_]public_ccs(ccs);

@*/

int serialize_to_public_message(char** dest, struct item* item);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*& 
               [?f1]item(item, ?i, pub) &*& *dest |-> _ &*& 
               [_]pub(i); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*& 
               [f1]item(item, i, pub) &*& pointer(dest, ?d) &*& 
               malloc_block(d, result) &*& result > 1 &*&
               chars(d, result, ?cs) &*&
               [_]item_constraints(i, cs_to_ccs(cs), pub); @*/

#endif
