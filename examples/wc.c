#include "stdlib.h"
#include "stdio.h"

/*@
fixpoint int wcount(chars cs, bool inword) {
  switch(cs) {
    case chars_nil: return 0;
    case chars_cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}
@*/

int wc(char* string, bool inword)
  //@ requires [?f]chars(string, ?cs) &*& chars_contains(cs, 0) == true;  
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

int main() 
  //@ requires true;
  //@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
  return 0;
}