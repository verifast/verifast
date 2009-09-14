#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

/*
Prints the contents of test.txt to stdout.
*/
int main()
  //@ requires true;
  //@ ensures true;
{
  struct file* fp = fopen("test.txt", "r+");
  char* buffer = malloc(sizeof(char) * 100);
  char* res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  res = fgets(buffer, 100, fp);
  while(res != 0) 
    //@ invariant file(fp) &*& chars(buffer, ?cs) &*& chars_length(cs) == 100 &*& res != 0 ? chars_contains(cs, 0) == true : true;
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  free(buffer);
  fclose(fp);
  return 0;
}