#ifndef DESERIALIZATION_H
#define DESERIALIZATION_H

#include "general.h"
#include "invariants.h"
#include "item_constraints.h"

/*@

lemma void deserialize_item(list<char> cs, predicate(item) pub);
  requires collision_in_run() == false &*&
           proof_obligations(pub) &*&
           length(cs) <= INT_MAX &*&
           true == well_formed(cs, nat_length(cs)) &*&
           true == polarssl_cryptograms_in_chars_upper_bound(
               cs, polarssl_generated_public_cryptograms(polarssl_pub(pub)));
  ensures  proof_obligations(pub) &*&
           [_]item_constraints_no_collision(?i, cs, pub) &*& [_]pub(i);

@*/

void parse_item(char* message, int size);
  /*@ requires [?f]chars(message, size, ?cs) &*& size > 1; @*/
  /*@ ensures  [f]chars(message, size, cs) &*&
               true == well_formed(cs, nat_length(cs)); @*/

struct item* deserialize_from_public_message(char* buffer, int size);
  /*@ requires [?f0]world(?pub) &*& 
               [?f1]polarssl_public_message(polarssl_pub(pub)) 
                                           (buffer, size, ?cs); @*/
  /*@ ensures  [f0]world(pub) &*& 
               [f1]polarssl_public_message(polarssl_pub(pub)) 
                                          (buffer, size, cs) &*&
               item(result, ?i, pub) &*& [_]pub(i); @*/

#endif
