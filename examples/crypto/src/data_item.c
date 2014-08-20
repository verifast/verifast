#include "data_item.h"

struct item *create_data_item(int data)
  //@ requires emp;
  //@ ensures  item(result, data_item(data));
{
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}
  item->tag = 0;
  item->size = (int) sizeof(int);
  item->content = malloc_wrapper(item->size);
  memcpy(item->content, &data, sizeof(int));
  
  //@ chars_to_integer(&data);
  //@ close item(item, data_item(data));
  return item;
}

bool is_data(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  item(item, i) &*&
        switch (i)
        {
          case data_item(d0):
            return result == true;
          case pair_item(f0, s0):
            return result == false;
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
{
  //@ open item(item, i);
  return item->tag == 0;
  //@ close item(item, i);
}

void check_is_data(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures 
        switch (i)
        {
          case data_item(d0):
            return item(item, i);
          case pair_item(f0, s0):
            return false;
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
{
  if (!is_data(item))
    abort_crypto_lib("Presented item is not a data item");
}

int item_get_data(struct item *item)
  //@ requires item(item, ?i);
  /*@ ensures  
        switch (i)
        {
          case data_item(d0):
            return item(item, i) &*& 
                   collision_in_run() ? true : result == d0;
          case pair_item(f0, s0):
            return false;
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
{
  check_is_data(item);
  //@ assert item(item, data_item(?d0));
  //@ open item(item, i);
  
  int* temp = (void*) item->content;
  if (item->size != (int) sizeof(int))
    abort_crypto_lib("Illegal size for data item");
  //@ chars_to_integer(item->content);
  return *temp;

  //@ close item(item, i);
}

