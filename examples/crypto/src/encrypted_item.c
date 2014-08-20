#include "encrypted_item.h"

#include "item.h"
#include "principals.h"

#include <string.h>

void check_valid_encrypted_item_size(int size)
  //@ requires true;
  //@ ensures  size > sizeof(char) + 2 * sizeof(int);
{
  if (size <= (int) sizeof(char) + 2 * (int) sizeof(int))
    abort_crypto_lib("Illegal size for encrypted item");
}

void check_valid_encrypted_item_chars_size(int cs_size)
  //@ requires true;
  //@ ensures  cs_size > sizeof(char);
{
  if (cs_size <= (int) sizeof(char))
    abort_crypto_lib("Illegal size for encrypted item");
}

bool is_encrypted(struct item *item)
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

{
  //@ open item(item, i);
  return item->tag == 5;
  //@ close item(item, i);
}

void check_is_encrypted(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures
        switch (i)
        {
          case data_item(d0):
            return false;
          case pair_item(f0, s0):
            return false;
          case nonce_item(p0, c0, inc0, i0):
            return false;
          case key_item(p0, c0, k0, i0):
            return false;
         case hmac_item(key0, pay0):
            return false;
          case encrypted_item(key0, pay0, ent0):
            return item(item, encrypted_item(key0, pay0, ent0));
        };
  @*/
{
  if (!is_encrypted(item))
    abort_crypto_lib("Presented item is not an encrypted item");
}
