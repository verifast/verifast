#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

/*
Prints the contents of given file to stdout.
*/
int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]char_array(argv, argc);
  //@ ensures true;
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { puts("Enter a file name."); return -1; }
  //@ open [_]char_array(argv, argc);
  //@ open [_]char_array(argv + 1, argc - 1);
  fp = fopen(* (argv + 1), "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  res = fgets(buffer, 100, fp);
  while(res != 0) 
    //@ invariant file(fp) &*& chars(buffer, ?cs) &*& length(cs) == 100 &*& res != 0 ? mem('\0', cs) == true : true;
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  free(buffer);
  fclose(fp);
  return 0;
}