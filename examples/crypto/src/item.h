#ifndef ITEM_H
#define ITEM_H

#include "general.h"

struct item
{
  int size;
  char* content;
};

/*@

predicate item_constraints(bool collision, item i, list<char> cs, 
                           predicate(item) pub);
predicate item_constraints_no_collision(item i, list<char> cs, 
                                        predicate(item) pub);

predicate item(struct item *item, item i, predicate(item) pub) =
  item != 0 &*&
  item->size |-> ?size &*&
    size > 1 &*&
  item->content |-> ?content &*&
    chars(content, size, ?cs) &*&
    malloc_block_chars(content, size) &*&
  malloc_block_item(item) &*&

  [_]item_constraints(_, i, cs, pub)
;

lemma_auto void non_zero_items()
  requires item(?item, ?i, ?pub);
  ensures  item(item, i, pub) &*& item != 0;
{
  open item(item, i, pub);
  close item(item, i, pub);
}

@*/

#endif
