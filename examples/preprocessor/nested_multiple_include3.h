#ifndef NESTED_MULTIPLE_INCLUDE3_H
#define NESTED_MULTIPLE_INCLUDE3_H

#include "nested_multiple_include.h"

/*@
#define NIL Nil
@*/

/*@

fixpoint Stack Push(void* item, any info, Stack Stack)
{
  switch ( Stack )
  {
    case NIL:
      return Cons(item, info, Stack);

    case Cons(x, y, z):
      return Cons(item, info, Stack);
  }
}

lemma void RewritePushCons(void* item, any info, Stack Stack)
  requires emp;
  ensures Push(item, info, Stack) == Cons(item, info, Stack);
{
  switch ( Stack )
  {
    case NIL:
    case Cons(x, y, z):
  }
}

fixpoint Stack Pop(Stack Stack)
{
  switch ( Stack )
  {
    case NIL:
      return NIL;

    case Cons(x, y, T):
      return T;
  }
}

fixpoint bool IsEmpty(Stack S)
{
  switch ( S )
  {
    case NIL:
      return true;
    
    case Cons(x, y, T):
      return false;
  }
}

@*/

#endif
