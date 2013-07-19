#ifndef NESTED_MULTIPLE_INCLUDE1_H
#define NESTED_MULTIPLE_INCLUDE1_H

#include "nested_multiple_include3.h"

/*@
#define STACK Stack
@*/

/*@

lemma void IsEmptyNil(STACK S)
  requires emp;
  ensures IsEmpty(S) ? S == NIL : emp;
{
  switch ( S )
  {
    case NIL:
    case Cons(x, y, z):
  }
}

lemma void SizeEmptyStack(STACK S)
  requires emp;
  ensures IsEmpty(S) ? Size(S) == 0 : true;
{
  switch ( S )
  {
    case NIL:
    case Cons(x, y, z):
  }
}

lemma void SizePush(void* data, any info, STACK S)
  requires emp;
  ensures Size( Push(data, info, S) ) == Size(S) + 1;
{
  switch ( S )
  {
    case NIL:
    case Cons(x, y, z):
  }
}


fixpoint void* GetTopPointer(STACK S)
{
  switch ( S )
  {
    case NIL:
      return 0;

    case Cons(x, y, z):
      return x;
  }  
}

lemma void PushNotNil(void* data, any info, STACK STACK)
  requires emp;
  ensures Push(data, info, STACK) != NIL;
{
  switch ( STACK )
  {
    case NIL:
    case Cons(x, y, z):
  }
}

@*/

#endif

