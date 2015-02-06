#include "data_item.h"

#include "item_constraints.h"

bool is_data(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == data_item(_) : true; @*/
{
  //@ open item(item, i, pub);
  //@ open chars(item->content, ?size, ?cs);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'a';
  //@ close item(item, i, pub);
}

void check_is_data(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == data_item(_);
{
  if (!is_data(item))
    abort_crypto_lib("Presented item is not a data item");
}

struct item *create_data_item(char* data, int length)
  /*@ requires [?f]world(?pub) &*&
               chars(data, length, ?cs) &*& length > 0; @*/
  /*@ ensures  [f]world(pub) &*&
               chars(data, length, cs) &*& 
               item(result, data_item(cs), pub); @*/
{
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}
  if (length >= INT_MAX - 1) abort_crypto_lib("Requested data item was to big");
  item->size = 1 + length;
  item->content = malloc_wrapper(item->size);
  *(item->content) = 'a';
  memcpy(item->content + 1, data, (unsigned int) length);
  //@ assert item->content |-> ?cont &*& item->size |-> ?size;
  //@ assert chars(cont, size, ?cs1);
  //@ item d = data_item(cs);
  //@ close item_constraints_no_collision(d, cs1, pub);
  //@ leak item_constraints_no_collision(d, cs1, pub);
  //@ close item_constraints(false, d, cs1, pub);
  //@ leak item_constraints(false, d, cs1, pub);
  //@ close item(item, d, pub);
  return item;
}

struct item *create_data_item_from_char(char i)
  //@ requires [?f]world(?pub);
  /*@ ensures  [f]world(pub) &*&
               item(result, data_item(cons(i, nil)), pub); @*/
{
  return create_data_item(&i, (int) sizeof(char));
}

int item_get_data(struct item *item, char** data)
  //@ requires item(item, ?i, ?pub) &*& i == data_item(?cs0) &*& pointer(data, _);
  /*@ ensures  item(item, i, pub) &*& pointer(data, ?p) &*&
               chars(p, result, ?cs1) &*& malloc_block(p, result) &*&
               collision_in_run() ? true : cs0 == cs1; @*/
{
  //@ open item(item, data_item(cs0), pub);
  //@ assert item->content |-> ?cont;
  //@ assert chars(cont, _, ?cs);
  //@ chars_limits(cont);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);

  int size = item->size - 1;
  char* temp = malloc_wrapper(size);
  memcpy(temp, (void*) item->content + 1, (unsigned int) size);
  
  //@ close item(item, data_item(cs0), pub);
  *data = temp;
  return size;
}

char item_get_data_as_char(struct item *item)
  //@ requires item(item, ?i, ?pub) &*& i == data_item(?cs0);
  /*@ ensures  item(item, i, pub) &*& 
               collision_in_run() ? true : cs0 == cons(result, nil); @*/
{
  //@ open item(item, data_item(cs0), pub);
  //@ assert item->content |-> ?cont;
  //@ assert chars(cont, _, ?cs);
  //@ chars_limits(cont);
  //@ open [_]item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  
  char* temp = item->content + 1;
  if (item->size != (int) sizeof(char) + 1)
    abort_crypto_lib("Illegal size for char data item");
  
  //@ open chars(cont, 2, cs);
  //@ open chars(temp, 1, _);
  return *temp;
  //@ close chars(temp, 1, _);
  //@ close item(item, i, pub);
}
