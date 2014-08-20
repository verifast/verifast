#ifndef SERIALIZATION_H
#define SERIALIZATION_H

#include "item.h"

/*@ 

fixpoint bool serialization_constraints(item i, list<char> serialized_item)
{
  return if_no_collision(
      // serialized_item is correct serialization
      serialized_item == extended_chars_for_item(i) &&
      item_constraints(i, tag_for_item(i), 
                  length(chars_for_item(i)), chars_for_item(i)) &&
      // lengths of parts of serialized_item are correct
      length(chars_of_int(tag_for_item(i))) == sizeof(int) &&
      0 < length(chars_for_item(i)) && length(chars_for_item(i)) < INT_MAX &&
      length(chars_of_int(length(chars_for_item(i)))) == sizeof(int) &&
      length(chars_for_item(i)) > 0
    );
}

predicate deserialization_attempt(item i, list<char> serialized_item) = true;

@*/

int item_serialize(char** dest, struct item* item);
  //@ requires [?f0]world(?pub) &*& item(item, ?i) &*& pointer(dest, ?d0);
  /*@ ensures  [f0]world(pub) &*& item(item, i) &*& pointer(dest, ?d) &*&
               malloc_block(d, result) &*& chars(d, result, ?cs) &*&
               result > 0 &*& serialization_constraints(i, cs) == true;
  @*/

struct item* item_deserialize(char* buffer, int size);
  /*@ requires [?f0]world(?pub) &*& [?f1]chars(buffer, size, ?cs) &*&
               deserialization_attempt(?i1, cs) &*&
               serialization_constraints(i1, cs) == true; @*/
  /*@ ensures  [f0]world(pub) &*& [f1]chars(buffer, size, cs) &*&
               item(result, ?i2) &*& result != 0 &&
               if_no_collision(i1 == i2); @*/

#endif
