#include "debug.h"

#include "general.h"
#include "item.h"

void debug_print(const char *message)
  //@ requires [?f]string(message, ?cs);
  //@ ensures  [f]string(message, cs);
{
#ifdef DEBUG
  printf("<DEBUG>%s\n", message);
#endif
}

void print_buffer(const char *buffer, int size)
  //@ requires [?f]chars(buffer, size, ?cs);
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
  //@ requires [?f]item(item, ?i, ?pub);
  //@ ensures  [f]item(item, i, pub);
{
#ifdef DEBUG
  //@ open [f]item(item, i, pub);
  printf("---------------------\n");
  printf("Item: %p\n", item);
  printf("\tsize %i\n", item->size);
  printf("\ttag: %c\n", *(item->content));
  printf("\tcontent:");
  print_buffer(item->content + 1, item->size - 1);
  printf("---------------------\n");
  //@ close  [f]item(item, i, pub);
#else
#endif
}
