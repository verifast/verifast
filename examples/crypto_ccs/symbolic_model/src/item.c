#include "item.h"

void item_free(struct item* item)
  //@ requires item(item, _, _);
  //@ ensures  true;
{
  //@ open item(item, _, _);
  zeroize(item->content, item->size);
  free(item->content);
  free(item);
}

struct item* item_clone(struct item* item)
  //@ requires [?f]item(item, ?i, ?pub);
  /*@ ensures  [f]item(item, i, pub) &*&
               item(result, i, pub) &*& result != 0; @*/
{
  //@ open [f]item(item, i, pub);
  struct item* clone = malloc(sizeof(struct item));
  if (clone == 0){abort_crypto_lib("malloc of item failed");}
  clone->size = item->size;
  clone->content = malloc_wrapper(clone->size);
  crypto_memcpy(clone->content, item->content, (unsigned int) clone->size);
  return clone;
  //@ close [f]item(item, i, pub);
  //@ close item(clone, i, pub);
}
