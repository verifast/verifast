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
  //@ requires [?f]crypto_chars(?kind, buffer, size, ?ccs);
  //@ ensures  [f]crypto_chars(kind, buffer, size, ccs);
{
#ifdef DEBUG
  int i = 0;
  while (i < size)
  {
    if (i % 32 == 0)
      printf("\n");
    printf("%x", (unsigned char) buffer[i]);
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
  printf("---------------------\n");
  printf("Item: %p\n", item);
  printf("\tsize %i\n", item->size);
  printf("\ttag: %c\n", *(item->content));
  printf("\tcontent:");
  print_buffer(item->content + 1, item->size - 1);
  printf("---------------------\n");
#else
#endif
}
