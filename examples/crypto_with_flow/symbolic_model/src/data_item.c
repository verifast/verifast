#include "data_item.h"

#include "item_constraints.h"

bool is_data(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == data_item(_) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == 'a';
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_data(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*& 
               i == data_item(_); @*/
{
  if (!is_data(item))
    abort_crypto_lib("Presented item is not a data item");
}

struct item *create_data_item(char* data, int length)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               chars(data, length, ?cs) &*& length >= MIN_DATA_SIZE; @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               chars(data, length, cs) &*& 
               item(result, data_item(cs), pub); @*/
{
  //@ open [f]world(pub, key_clsfy);
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}
  if (length >= INT_MAX - TAG_LENGTH) abort_crypto_lib("Requested data item was to big");
  item->size = TAG_LENGTH + length;
  item->content = malloc_wrapper(item->size);
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  write_tag(item->content, TAG_DATA);
  //@ chars_to_crypto_chars(data, length);
  memcpy(item->content + TAG_LENGTH, data, (unsigned int) length);
  //@ crypto_chars_to_chars(cont + TAG_LENGTH, length);
  //@ assert chars(cont, TAG_LENGTH, full_tag(TAG_DATA));
  //@ assert chars(cont + TAG_LENGTH, length, cs);
  //@ chars_join(cont);
  //@ assert chars(cont, size, ?cs1);
  //@ assert cs1 == append(full_tag(TAG_DATA), cs);
  //@ take_append(TAG_LENGTH, full_tag(TAG_DATA), cs);
  //@ drop_append(TAG_LENGTH, full_tag(TAG_DATA), cs);
  //@ head_append(full_tag(TAG_DATA), cs);
  
  //@ item d = data_item(cs);
  
  //@ assert length(cs1) > TAG_LENGTH;
  //@ assert true == valid_tag(head(cs1));
  //@ assert take(TAG_LENGTH, cs1) == full_tag(head(cs1));
  //@ assert head(cs1) == TAG_DATA;
  //@ length_equals_nat_length(cs1);
  //@ switch(nat_length(cs1)) {case succ(s0): case zero:}
  //@ close ic_parts(d)(full_tag(TAG_DATA), cs);
  //@ public_chars(cont, TAG_LENGTH);
  //@ public_chars(data, length);
  //@ public_generated_join(polarssl_pub(pub), full_tag(TAG_DATA), cs);
  //@ close item_constraints(d, cs1, pub);
  //@ leak item_constraints(d, cs1, pub);
  //@ chars_join(cont);
  //@ chars_to_secret_crypto_chars(cont, length(cs1));
  //@ close item(item, d, pub);
  return item;
  //@ close [f]world(pub, key_clsfy);
}

struct item *create_data_item_from_int(int i)
  //@ requires [?f]world(?pub, ?key_clsfy);
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(result, data_item(chars_of_int(i)), pub); @*/
{
  char* temp = (void*) &i;
  //@ integer_to_chars(temp);
  return create_data_item(temp, (int) sizeof(int));
  //@ chars_to_integer(temp);
}

int item_get_data(struct item *item, char** data)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub) &*& 
               i == data_item(?cs0) &*& pointer(data, _); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*& pointer(data, ?p) &*&
               chars(p, result, ?cs1) &*& malloc_block(p, result) &*&
               col || cs0 == cs1; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, data_item(cs0), pub);
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  //@ open [_]item_constraints(i, ?cs, pub);
  int data_size = item->size - TAG_LENGTH;
  //@ crypto_chars_limits(cont);
  //@ crypto_chars_split(cont, TAG_LENGTH);
  char* temp = malloc_wrapper(data_size);
  //@ public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
  //@ public_crypto_chars(cont + TAG_LENGTH, data_size);
  //@ chars_to_crypto_chars(cont + TAG_LENGTH, data_size);
  memcpy(temp, (void*) item->content + TAG_LENGTH, (unsigned int) data_size);
  //@ chars_to_secret_crypto_chars(cont + TAG_LENGTH, data_size);
  //@ crypto_chars_join(cont);
  //@ drop_append(TAG_LENGTH, full_tag(TAG_DATA), cs0);
  //@ close item(item, data_item(cs0), pub);
  *data = temp;
  return data_size;
  //@ close [f]world(pub, key_clsfy);  
}

int item_get_data_as_int(struct item *item)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub) &*& 
               i == data_item(?cs0); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               col ?  true : result == int_of_chars(cs0); @*/
{
  int result;
  char* data;
  int size = item_get_data(item, &data);
  if (size != (int) sizeof(int)) abort();
  //@ chars_to_integer(data);
  result = *((int*) ((void*) data));
  free(data);
  return result;
}
