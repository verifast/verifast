#include "debug.h"

#include "general.h"
#include "item.h"

#ifdef DEBUG
int indent;
#endif

/*@

predicate debug_initialized() =
#ifdef DEBUG
  integer(&indent, ?i) &*&
#endif
  true
;

@*/

void debug_init()
  //@ requires module(debug, true);
  //@ ensures  debug_initialized();
{
  //@ open_module();
#ifdef DEBUG
  indent = 0;
#endif
  //@ close debug_initialized();
}

void debug_exit()
  //@ requires debug_initialized();
  //@ ensures  module(debug, false);
{
  //@ open debug_initialized();
  //@ close_module();
}

void debug_print(const char *message)
  //@ requires [?f]string(message, ?cs);
  //@ ensures  [f]string(message, cs);
{
#ifdef DEBUG
  printf("<DEBUG>%s\n", message);
#endif
}

void print_buffer(const char *buffer, int size)
  //@ requires [?f]chars(buffer, size, ?cs) &*& size < INT_MAX;
  //@ ensures  [f]chars(buffer, size, cs);
{
#ifdef DEBUG
  int i = 0;
  while (i < size)
    //@ requires [f]chars(buffer + i, size - i, ?cs0);
    //@ ensures  [f]chars(buffer + old_i, size - old_i, cs0);
  {
    if (i % 32 == 0)
      printf("\n");

    //@ open  [f]chars(buffer + i, size - i, cs0);
    printf("%x", (unsigned char) buffer[i]);
    //@ close [f]chars(buffer + old_i, size - old_i, cs0);

    i++;
  }
  printf("\n");
#endif
}

void print_item(const struct item* item)
  //@ requires [?f]item(item, ?i);
  //@ ensures  [f]item(item, i);
{
#ifdef DEBUG
  //@ open [f]item(item, i);
  printf("---------------------\n");
  printf("Item: %p\n", item);
  printf("\ttag %i\n", item->tag);
  printf("\tsize %i\n", item->size);
  printf("\tcontent:");
  if (item->content == 0)
    printf("\t[empty]");
  else
    print_buffer(item->content, item->size);
  printf("---------------------\n");
  //@ close  [f]item(item, i);
#else
#endif
}
