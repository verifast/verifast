#ifndef DESERIALIZATION_H
#define DESERIALIZATION_H

#include "general.h"
#include "invariants.h"
#include "item_constraints.h"

/*@

lemma void deserialize_item(list<char> cs, predicate(item) pub);
  requires proof_obligations(pub) &*&
           length(cs) <= INT_MAX &*&
           true == well_formed(cs, nat_length(cs)) &*&
           [_]public_generated(polarssl_pub(pub))(cs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(?i, cs, pub) &*& [_]pub(i);

@*/

void parse_item(char* buffer, int size);
  /*@ requires [?f1]world(?pub) &*&
               [?f2]crypto_chars(?kind, buffer, size, ?cs) &*&
               kind != garbage &*& size > TAG_LENGTH &*&
               kind == normal ? true :
                 [_]item_constraints(?i, cs, pub); @*/
  /*@ ensures  [f1]world(pub) &*&
               [f2]crypto_chars(kind, buffer, size, cs) &*&
               true == well_formed(cs, nat_length(cs)); @*/

struct item* deserialize(char* buffer, int size);
  /*@ requires [?f0]world(?pub) &*&
               [?f1]chars(buffer, size, ?cs); @*/
  /*@ ensures  [f0]world(pub) &*&
               [f1]chars(buffer, size, cs) &*&
               item(result, ?i, pub) &*& [_]pub(i); @*/

#endif
