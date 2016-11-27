#ifndef DESERIALIZATION_H
#define DESERIALIZATION_H

#include "general.h"
#include "invariants.h"
#include "item_constraints.h"

/*@

lemma item deserialize_item(list<crypto_char> ccs);
  requires FORALLP_C &*& FORALLP_CS &*& 
           proof_obligations(?pub) &*& [_]public_invar(polarssl_pub(pub)) &*&
           length(ccs) <= INT_MAX &*&
           true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs) &*&
           [_]public_ccs(ccs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints(result, ccs, pub) &*& [_]pub(result);

@*/

void parse_item(char* buffer, int size);
  /*@ requires FORALLP_C &*& FORALLP_CS &*& 
               [?f1]world(?pub, ?key_clsfy) &*&
               [?f2]crypto_chars(?kind, buffer, size, ?ccs) &*&
               size > TAG_LENGTH &*&
               kind == normal ? true :
                 [_]item_constraints(?i, ccs, pub); @*/
  /*@ ensures  [f1]world(pub, key_clsfy) &*&
               [f2]crypto_chars(kind, buffer, size, ccs) &*&
               true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs); @*/

struct item* deserialize(char* buffer, int size);
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]chars(buffer, size, ?cs); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]chars(buffer, size, cs) &*&
               item(result, ?i, pub) &*& [_]pub(i); @*/

#endif
