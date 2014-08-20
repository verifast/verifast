#include "serialization.h"

#include "item.h"
#include "principals.h"

int item_serialize(char** dest, struct item* item)
  //@ requires [?f0]world(?pub) &*& item(item, ?i) &*& pointer(dest, ?d0);
  /*@ ensures  [f0]world(pub) &*& item(item, i) &*& pointer(dest, ?d) &*&
               malloc_block(d, result) &*& chars(d, result, ?cs) &*&
               result > 0 &*& serialization_constraints(i, cs) == true;
  @*/
{
  //@ open item(item, i);
  int size = (int) sizeof(int) + (int) sizeof(int) + item->size;
  char *buffer = malloc_wrapper(size);
  *dest = buffer;

  //@ integer_to_chars(&(item->tag));
  write_buffer(&buffer, (void *) &(item->tag), (int) sizeof(int));
  //@ chars_to_integer(&(item->tag));
  //@ integer_to_chars(&(item->size));
  write_buffer(&buffer, (void *) &(item->size), (int) sizeof(int));
  //@ chars_to_integer(&(item->size));
  write_buffer(&buffer, (void *) item->content, (int) item->size);

  return size;
  //@ chars_join(*dest);
  //@ chars_join(*dest);
  //@ close item(item, i);

  /*@ 
    append_assoc(chars_of_int(tag_for_item(i)),
                    chars_of_int(length(chars_for_item(i))), 
                      chars_for_item(i));
  @*/
}

struct item* item_deserialize(char* buffer, int size)
  /*@ requires [?f0]world(?pub) &*& [?f1]chars(buffer, size, ?cs) &*&
               deserialization_attempt(?i1, cs) &*&
               serialization_constraints(i1, cs) == true; @*/
  /*@ ensures  [f0]world(pub) &*& [f1]chars(buffer, size, cs) &*&
               item(result, ?i2) &*& result != 0 &&
               if_no_collision(i1 == i2); @*/
{
  //@ open deserialization_attempt(i1, cs);
  
  struct item* result = malloc(sizeof(struct item));
  if (result == 0){abort_crypto_lib("malloc of item failed");}
  
  //@ close [f1/2]hide_chars(buffer, size, cs);
  check_valid_item_size(size);
  
  //@ chars_limits(buffer);
  int* temp = (void*) buffer;
  //@ chars_split(buffer, sizeof(int));
  //@ chars_to_integer(temp);
  int tag = *(temp);
  if (tag < 0 || tag > 5)
    abort_crypto_lib("Illegal tag");
  result->tag = tag;
  //@ integer_to_chars(temp);
  check_valid_item_tag(tag);
  
  temp++;
  //@ chars_to_integer(temp);
  result->size = *(temp);
  //@ integer_to_chars(temp);
  check_valid_item_sizes(size, result->size);
    
  temp++;
  result->content = malloc_wrapper(result->size);
  char* item_chars = (void*) temp;
  
  //@ int tag_r = tag_for_item(i1);
  //@ int size_r = length(chars_for_item(i1));
  //@ list<char> cs_1 = chars_of_int(tag_r);
  //@ list<char> cs_2 = chars_of_int(size_r);
  //@ list<char> cs_r = chars_for_item(i1);
  //@ take_append(sizeof(int), cs_1, append(cs_2, cs_r));
  //@ drop_append(sizeof(int), cs_1, append(cs_2, cs_r));
  /*@ 
    if (collision_in_run() == false) 
    {
      take_append(sizeof(int), cs_2, cs_r);
      drop_append(sizeof(int), cs_2, cs_r);
    }
  @*/
  memcpy(result->content, item_chars, (unsigned int) result->size);

  if (result == 0)
    abort_crypto_lib("Deserializing failed: null is not a valid item");
  /*@
    if (collision_in_run() == false) 
    {
      close item(result, i1);
    }
    else
    {
      dummy_item_for_tag_has_valid_tag(tag);
      close item(result, dummy_item_for_tag(tag));
    }
  @*/ 
  //@ chars_join(buffer + sizeof(int));
  //@ chars_join(buffer);
  //@ open [f1/2]hide_chars(buffer, size, cs);
  return result;
}
