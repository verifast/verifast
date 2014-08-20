#ifndef PAIR_ITEM_H
#define PAIR_ITEM_H

#include "general.h"
#include "item.h"

// see ../include/cryptolib.h

void pair_get_components(struct item *pair, 
                         struct item **firstp, struct item **secondp);
  /*@ requires [?f]world(?pub) &*& item(pair, ?p) &*&
               pointer(firstp, _) &*& pointer(secondp, _); @*/
  /*@ ensures  [f]world(pub) &*& item(pair, p) &*&
               pointer(firstp, ?fp) &*& pointer(secondp, ?sp) &*&
        switch (p)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return item(fp, ?f1) &*& item(sp, ?s1) &*& 
                   true == if_no_collision(f0 == f1 && s0 == s1);
          case nonce_item(p0, c0, inc0, i0): 
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
          case hmac_item(k0, pay0):
            return false;
          case encrypted_item(k0, pay0, ent0):
            return false;
        };
  @*/

bool is_pair(struct item *item);
  //@ requires [?f]world(?pub) &*& item(item, ?i);
  /*@ ensures  [f]world(pub)   &*& item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == true;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return result == false;
          case hmac_item(k0, pay0):
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

#endif
