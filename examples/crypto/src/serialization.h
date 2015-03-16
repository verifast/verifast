#ifndef SERIALIZATION_H
#define SERIALIZATION_H

#include "invariants.h"
#include "general.h"
#include "item_constraints.h"

/*@

lemma void collision_public(predicate(item) pub, list<char> cs);
  requires true == collision_in_run();
  ensures  [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);

lemma void serialize_item(item i);
  requires proof_obligations(?pub) &*&
           [_]item_constraints_no_collision(i, ?cs, pub) &*&
           [_]pub(i);
  ensures  proof_obligations(pub) &*& 
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);

@*/

int serialize_to_public_message(char** dest, struct item* item);
  /*@ requires [?f0]world(?pub) &*& 
               [?f1]item(item, ?i, pub) &*& pointer(dest, _) &*& 
               [_]pub(i); @*/
  /*@ ensures  [f0]world(pub) &*& 
               [f1]item(item, i, pub) &*& pointer(dest, ?d) &*& 
               malloc_block(d, result) &*& result > 1 &*&
               polarssl_public_message(polarssl_pub(pub))
                                      (d, result, ?cs) &*&
               [_]item_constraints(_, i, cs, pub); @*/

#endif
