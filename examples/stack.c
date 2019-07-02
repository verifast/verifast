#include "stdlib.h"

/*
  Destructors
*/

/*@

predicate_family Ownership(void* destructor)(void* data, any info);

@*/

typedef void destructor(void* data);
  //@ requires Ownership(this)(data, _);
  //@ ensures emp;
  

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*@

inductive Stack =
  | Nil
  | Cons(void* data, any info, Stack);

predicate Node(struct node* node, void* data, destructor* destructor, struct node* next, any info) =
  malloc_block_node( node ) &*&
  node->data |-> data &*&
  node->next |-> next &*&
  Ownership(destructor)(data, info) &*&
  is_destructor(destructor) == true &*&
  node != 0;

predicate StackItems(struct node* head, destructor* destructor, Stack S) =
  is_destructor(destructor) == true &*&
  head == 0 ? S == Nil :
  Node(head, ?data, destructor, ?next, ?info) &*&
  StackItems(next, destructor, ?T) &*&
  S == Cons(data, info, T);

predicate Stack(struct stack* stack, destructor* destructor, Stack S) =
  malloc_block_stack(stack) &*&
  is_destructor(destructor) == true &*&
  stack->destructor |-> destructor &*&
  stack->first |-> ?first &*&
  stack->size |-> ?size &*&
  size == Size(S) &*&
  StackItems(first, destructor, S);

fixpoint Stack Push(void* item, any info, Stack Stack)
{
  switch ( Stack )
  {
    case Nil:
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
    case Nil:
    case Cons(x, y, z):
  }
}

fixpoint Stack Pop(Stack Stack)
{
  switch ( Stack )
  {
    case Nil:
      return Nil;

    case Cons(x, y, T):
      return T;
  }
}

fixpoint bool IsEmpty(Stack S)
{
  switch ( S )
  {
    case Nil:
      return true;
    
    case Cons(x, y, T):
      return false;
  }
}

lemma void IsEmptyNil(Stack S)
  requires emp;
  ensures IsEmpty(S) ? S == Nil : emp;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

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

lemma void SizeEmptyStack(Stack S)
  requires emp;
  ensures IsEmpty(S) ? Size(S) == 0 : true;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

lemma void SizePush(void* data, any info, Stack S)
  requires emp;
  ensures Size( Push(data, info, S) ) == Size(S) + 1;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}


fixpoint void* GetTopPointer(Stack S)
{
  switch ( S )
  {
    case Nil:
      return 0;

    case Cons(x, y, z):
      return x;
  }  
}

lemma void PushNotNil(void* data, any info, Stack Stack)
  requires emp;
  ensures Push(data, info, Stack) != Nil;
{
  switch ( Stack )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

@*/

struct stack* create_empty_stack(destructor* destructor)
  //@ requires is_destructor(destructor) == true;
  //@ ensures Stack(result, destructor, ?Stack) &*& IsEmpty(Stack) == true;
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close StackItems(0, destructor, Nil);
  //@ close Stack(stack, destructor, Nil);
  
  return stack;
}

void destroy_stack(struct stack* stack)
  //@ requires Stack(stack, _, ?S);
  //@ ensures emp;
{
  //@ open Stack(stack, _, S);
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
  //@ requires Stack(stack, ?destructor, ?Stack) &*& Ownership(destructor)(data, ?info);
  //@ ensures Stack(stack, destructor, Push(data, info, Stack));
{
  //@ open Stack(stack, destructor, Stack);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  //@ close Node(node, data, destructor, stack->first, info);
  //@ RewritePushCons(data, info, Stack);
  //@ close StackItems(node, destructor, Push(data, info, Stack));
  
  stack->first = node;
  stack->size++;
  //@ close Stack(stack, destructor, Push(data, info, Stack));
}

void* pop(struct stack* stack)
  /*@
  requires Stack(stack, ?destructor, Cons(?head, ?info, ?tail));
  @*/
  /*@
  ensures Stack(stack, destructor, tail) &*&
          Ownership(destructor)(head, info) &*& result == head;
  @*/
{
  //@ open Stack(stack, destructor, ?Stack);
  struct node* first = stack->first;
  //@ open StackItems(first, destructor, _);
  //@ open Node(first, _, _, _, _);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  stack->size--;
  //@ close Stack(stack, destructor, tail);
  
  return data;
}

destructor* get_destructor(struct stack* stack)
  //@ requires Stack(stack, ?destructor, ?Stack);
  /*@
  ensures Stack(stack, destructor, Stack) &*&
          is_destructor(result) == true &*&
          result == destructor;
  @*/
{
  //@ open Stack(stack, destructor, Stack);
  destructor* d = stack->destructor;
  //@ close Stack(stack, destructor, Stack);
  return d;
}

void pop_destroy(struct stack* stack)
  //@ requires Stack(stack, ?destructor, ?Stack) &*& Stack != Nil;
  //@ ensures Stack(stack, destructor, Pop(Stack));
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}

bool is_empty(struct stack* stack)
  //@ requires Stack(stack, ?destructor, ?Stack);
  //@ ensures Stack(stack, destructor, Stack) &*& result == IsEmpty(Stack);
{
  //@ open Stack(stack, destructor, Stack);
  struct node* first = stack->first;
  //@ open StackItems(first, destructor, Stack);
  //@ close StackItems(first, destructor, Stack);
  //@ close Stack(stack, destructor, Stack);
  return first == 0;
}

int size(struct stack* stack)
  //@ requires Stack(stack, ?destructor, ?Stack);
  //@ ensures Stack(stack, destructor, Stack) &*& result == Size(Stack);
{
  //@ open Stack(stack, destructor, Stack);
  int size = stack->size;
  //@ close Stack(stack, destructor, Stack);
  return size;
}



/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

/*@

predicate Data(struct data* data, int foo, int bar) =
  malloc_block_data(data) &*&
  data->foo |-> foo &*&
  data->bar |-> bar;

@*/

struct data* create_data(int foo, int bar)
  //@ requires emp;
  //@ ensures Ownership(destroy_data)(result, DataCarrier(foo, bar));
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close Data(data, foo, bar);
  //@ close Ownership(destroy_data)(data, DataCarrier(foo, bar));
  return data;
}

/*
int get_foo(struct data* data)
  //@ requires Ownership(destroy_data)(data, ?DC);
  //@ ensures Ownership(destroy_data)(data, DC) &*& result == GetFoo(DC);
{
}
*/

/*@

inductive DataCarrier =
  | DataCarrier(int, int);

fixpoint int GetFoo(DataCarrier dc)
{
  switch ( dc )
  {
    case DataCarrier(x, y):
      return x;
  }
}

fixpoint int GetBar(DataCarrier dc)
{
  switch ( dc )
  {
    case DataCarrier(x, y):
      return y;
  }
}

predicate_family_instance Ownership(destroy_data)(struct data* data, DataCarrier dc) =
  Data(data, GetFoo(dc), GetBar(dc));

@*/

void destroy_data(struct data* data) //@ : destructor
  //@ requires Ownership(destroy_data)(data, _);
  //@ ensures emp;
{
  //@ open Ownership(destroy_data)(data, _);
  //@ open Data(data, _, _);
  free(data);
}

void check()
  //@ requires emp;
  //@ ensures emp;
{
  struct stack* stack = create_empty_stack(destroy_data);
  //@ assert Stack(stack, _, ?S0);
  //@ SizeEmptyStack(S0);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  //@ assert Stack(stack, _, ?S1);
  //@ SizePush(data, DataCarrier(1, 2), S0);
  //@ assert s == 1;
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  //@ assert Stack(stack, _, ?S2);
  //@ SizePush(data, DataCarrier(2, 3), S1);
  assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}

void check2()
  //@ requires emp;
  //@ ensures emp;
{
  struct stack* stack = create_empty_stack(destroy_data);
  //@ assert Stack(stack, _, ?InitStack);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);
  
  push(stack, d1);
  //@ assert Stack(stack, _, ?S);
  push(stack, d2);
  
  //@ PushNotNil(d2, DataCarrier(2, 2), S);
  struct data* d = pop(stack);
  //@ RewritePushCons(d2, DataCarrier(2, 2), S);
  //@ open Ownership(destroy_data)(d, ?DC);
  //@ open Data(d, ?foo, ?bar);
  //@ assert foo == 2;
  //@ assert bar == 2;
  //@ close Data(d, foo, bar);
  //@ close Ownership(destroy_data)(d, DC);
  destroy_data(d);
  
  //@ IsEmptyNil(InitStack);
  //@ PushNotNil(d1, DataCarrier(1, 1), Nil);
  d = pop(stack);
  //@ open Ownership(destroy_data)(d, ?DC2);
  //@ open Data(d, ?foo2, ?bar2);
  //@ assert foo2 == 1;
  //@ assert bar2 == 1;
  //@ close Data(d, foo2, bar2);
  //@ close Ownership(destroy_data)(d, DC2);
  
  destroy_data(d);
  
  destroy_stack(stack);
}

/*@

lemma void CheckPushPop(void* item, any info, Stack S)
  requires emp;
  ensures Pop( Push( item, info, S ) ) == S;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, T):
  }
}

lemma void CheckSizePush(void* item, any info, Stack S)
  requires emp;
  ensures Size( Push( item, info, S ) ) == 1 + Size( S );
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

@*/