#ifndef HASH_ITEM_H
#define HASH_ITEM_H

#include "general.h"
#include "item_constraints.h"

/*@

lemma void hash_item_payload(item i);
  nonghost_callers_only
  requires [?f]world(?pub, ?key_clsfy) &*&
           [_]item_constraints(i, ?ccs, pub) &*&
           [_]hash_item_payload(pub, _, i);
  ensures  [f]world(pub, key_clsfy) &*&
           [_]hash_payload(_, ccs);

@*/

#endif