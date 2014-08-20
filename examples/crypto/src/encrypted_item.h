#ifndef ENCRYPTED_ITEM_H
#define ENCRYPTED_ITEM_H

#include "general.h"

// see ../include/cryptolib.h

void check_valid_encrypted_item_size(int size);
  //@ requires true;
  //@ ensures  size > sizeof(char) + 2 * sizeof(int);

void check_valid_encrypted_item_chars_size(int cs_size);
  //@ requires true;
  //@ ensures  cs_size > sizeof(char);

bool is_encrypted(struct item *item);
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
            return result == false;
          case encrypted_item(k0, pay0, ent0):
            return result == true;
        };
  @*/

#endif
