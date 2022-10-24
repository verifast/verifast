#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  //@ open [_]argv(argv + 2, argc - 2, _);
  from = fopen(* (argv + 1), "r");
  to = fopen(* (argv + 2), "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
    //@ invariant file(from) &*& file(to) &*& buffer[..nb_read] |-> ?_ &*& nb_read <= 100 &*& buffer[nb_read..100] |-> _;
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    //@ chars_chars__join(buffer);
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}
