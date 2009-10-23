#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include "bool.h"
#include "assert.h"

int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]char_array(argv, argc);
  //@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  //@ open [_]char_array(argv, argc);
  //@ open [_]char_array(argv + 1, argc - 1);
  //@ open [_]char_array(argv + 2, argc - 2);
  from = fopen(* (argv + 1), "r");
  to = fopen(* (argv + 2), "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
    //@ invariant file(from) &*& file(to) &*& chars(buffer, ?cs) &*& length(cs) == 100 &*& nb_read <= 100;
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}