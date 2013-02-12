// Test that multiple includes of the same file are oke
//
// Headerfiles should be guarded if included mutliple times,
// otherwise secondary occurences are not skipped by the 
// context-free preprocessor and an exception will be thrown

#include "multiple_include.h"
#include "multiple_include2.h"
#include "multiple_include3.h"
#include "multiple_include.h"
#include "multiple_include2.h"
#include "multiple_include.h"
#include "multiple_include3.h"

int main() //@ : main
  //@ requires true;
  //@ ensures true; 
{
  int count = 20;
  increment(&count);
  decrement(&count);
  //@ assert count == 20;
  reset(&count);
  //@ assert count == 0;
  return 0;
}
