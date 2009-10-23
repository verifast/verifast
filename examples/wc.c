#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include "bool.h"
#include "assert.h"

// Counts the number of words in the given file.

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}
@*/

int wc(char* string, bool inword)
  //@ requires [?f]chars(string, ?cs) &*& mem('\0', cs) == true;  
  //@ ensures [f]chars(string, cs) &*& result == wcount(cs, inword);
{
  //@ open [f]chars(string, cs);
  char head = * string;
  if(head == 0) {
    //@ close [f]chars(string, cs);
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close [f]chars(string, cs);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close [f]chars(string, cs);
      return result;
    }
  }
}

void test() 
  //@ requires true;
  //@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]char_array(argv, argc);
  //@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  //@ open [_]char_array(argv, argc);
  //@ open [_]char_array(argv + 1, argc - 1);
  fp = fopen(* (argv + 1), "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
    //@ invariant file(fp) &*& chars(buff, ?cs) &*& length(cs) == 100 &*& res != 0 ? mem('\0', cs) == true : true;
  {
    int tmp = wc(buff, inword);
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  return 0;
}