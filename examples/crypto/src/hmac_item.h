#ifndef HMAC_ITEM_H
#define HMAC_ITEM_H

#include "general.h"

// see ../include/cryptolib.h

bool is_hmac(struct item *item);
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == false;
          case pair_item(f0, s0):
            return result == false;
          case nonce_item(p0, c0, inc0, i0):
            return result == false;
          case key_item(p0, c0, k0, i0):
            return result == false;
          case hmac_item(k0, pay0):
            return result == true;
          case encrypted_item(k0, pay0, ent0):
            return result == false;
        };
  @*/

#endif
