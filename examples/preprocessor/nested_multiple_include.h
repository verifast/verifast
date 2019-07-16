#ifndef NESTED_MULTIPLE_INCLUDE_H
#define NESTED_MULTIPLE_INCLUDE_H

#include "nested_multiple_include2.h"

/*@

inductive Stack =
  | Nil
  | Cons(void* data, any info, Stack);

predicate Node(struct node* node, void* data, destructor* destructor, struct node* next, any info) =
  malloc_block_node( node ) &*&
  node->data |-> data &*&
  node->next |-> next &*&
  OWNERSHIP(destructor, data, info) &*&
  ASSERT_TRUE(is_destructor(destructor)) &*&
  node != 0;

predicate StackItems(struct node* head, destructor* destructor, Stack S) =
  ASSERT_TRUE(is_destructor(destructor)) &*&
           (head == 0 ? S == Nil
                      : Node(head, ?data, destructor, ?next, ?info) &*&
                        StackItems(next, destructor, ?T) &*&
                        S == Cons(data, info, T));

predicate Stack(struct stack* stack, destructor* destructor, Stack S) =
  malloc_block_stack(stack) &*&
  ASSERT_TRUE(is_destructor(destructor)) &*&
  stack->destructor |-> destructor &*&
  stack->first |-> ?first &*&
  stack->size |-> ?size &*&
  size == Size(S) &*&
  StackItems(first, destructor, S);

fixpoint int Size(Stack S)
{
  switch ( S )
  {
    case Nil:
      return 0;
    
    case Cons(x, y, T):
      return 1 + Size(T);
  }
}

@*/

#endif
