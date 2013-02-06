#include <stdlib.h>

// Test of line concatenation using backslash.

#define XYZ

#ifdef XYZ
#define FOO 3 + 7
#else
this is nonsense
#endif

#undef XYZ

#ifndef XYZ
#define BAR(x,y) (x + y + FOO)
#else
more nonsense
#endif

#if defined(XYZ)
nonsensical nonsense
#elif defined XYZ
nonsense++
#else
#define BAZ 1
#endif

in\
t ma\
in()
  //@ re\
quires true;
  //@ ensures true;
{
  char *c = "A\
B";
  //@ open [_]string(c, _);
  char c0 = *c;
  //@ open [_]string(c + 1, _);
  char c1 = *(c + 1);
  assert(c0 == 'A' && c1 == 'B');
  assert(FOO == 10);
  assert(36 == BAR(10, 15) + BAZ);
  
#define COND 1

#ifdef COND
  int cond = 1;
#elif COND
  assert(false);
#else
  assert(false);
#endif
  assert(cond == 1);

#if 0
 #if 1
  assert(false);
 #else
  assert(false);
 #endif
  assert(false);
#else
  int cond2 = 1;
#endif
  assert(cond2 == 1);
  
  return 0;
}