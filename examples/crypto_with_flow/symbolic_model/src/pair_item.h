#ifndef PAIR_ITEM_H
#define PAIR_ITEM_H

#include "general.h"

void pair_get_components(struct item *pair, 
                         struct item **firstp, struct item **secondp);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(pair, ?p, pub) &*&
               p == pair_item(?f0, ?s0) &*&
               pointer(firstp, _) &*& pointer(secondp, _); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(pair, p, pub) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
                 item(fp, ?f1, pub) &*& item(sp, ?s1, pub) &*&
               col ? true : f0 == f1 && s0 == s1; @*/

#endif