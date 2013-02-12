// Test that multiple nested includes results in
// correct verification.
//
// Taken file stack.c from the examples: 
//   -split the declarations and annotations over multiple headers
//   -add macros everywhere

#include "nested_multiple_include.h"
#include "nested_multiple_include1.h"

struct stack* create_empty_stack(destructor* destructor)
  //@ requires ASSERT_TRUE(is_destructor(destructor));
  //@ ensures ASSERT_TRUE(Stack(result, destructor, ?Stack) &*& IsEmpty(Stack));
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close StackItems(0, destructor, NIL);
  //@ close STACK(stack, destructor, NIL);
  
  return stack;
}

void destroy_stack(struct stack* stack)
  //@ requires STACK(stack, _, ?S);
  //@ ensures emp;
{
  //@ open STACK(stack, _, S);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant StackItems(current, destructor, _);
  {
    //@ open StackItems(current, destructor, _);
    //@ open Node(current, _, _, _, _);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  
  //@ open StackItems(current, _, _);
  free(stack);
}

void push(struct stack* stack, void* data)
  //@ requires STACK(stack, ?destructor, ?Stack) &*& OWNERSHIP(destructor, data, ?info);
  //@ ensures STACK(stack, destructor, Push(data, info, STACK));
{
  //@ open STACK(stack, destructor, STACK);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  //@ close Node(node, data, destructor, stack->first, info);
  //@ RewritePushCons(data, info, STACK);
  //@ close StackItems(node, destructor, Push(data, info, STACK));
  
  stack->first = node;
  stack->size++;
  //@ close STACK(stack, destructor, Push(data, info, STACK));
}

void* pop(struct stack* stack)
  /*@
  requires STACK(stack, ?destructor, Cons(?head, ?info, ?tail));
  @*/
  /*@
  ensures STACK(stack, destructor, tail) &*&
          OWNERSHIP(destructor, head, info) &*& result == head;
  @*/
{
  //@ open STACK(stack, destructor, ?Stack);
  struct node* first = stack->first;
  //@ open StackItems(first, destructor, _);
  //@ open Node(first, _, _, _, _);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  stack->size--;
  //@ close STACK(stack, destructor, tail);
  
  return data;
}
