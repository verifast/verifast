#include "stdlib.h"

/*
  Destructors
*/

typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
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

inductive Stack<T> =
  | Nil
  | Cons(void* data, T info, Stack<T>);

predicate Node<T>(predicate(void *, T) Ownership, struct node* node, void *data, T info, struct node* next) =
  malloc_block_node( node ) &*&
  node->data |-> data &*&
  node->next |-> next &*&
  Ownership(data, info) &*&
  node != 0;

predicate StackItems<T>(predicate(void *, T) Ownership, struct node* head, Stack<T> S) =
  head == 0 ? S == Nil :
  Node(Ownership, head, ?data, ?info, ?next) &*&
  StackItems(Ownership, next, ?T) &*&
  S == Cons(data, info, T);

predicate Stack<T>(struct stack* stack, destructor* destructor, predicate(void *, T) Ownership, Stack<T> S) =
  malloc_block_stack(stack) &*&
  [_]is_destructor(destructor, Ownership) &*&
  stack->destructor |-> destructor &*&
  stack->first |-> ?first &*&
  stack->size |-> ?size &*&
  size == Size(S) &*&
  StackItems(Ownership, first, S);

fixpoint Stack<T> Push<T>(void* item, T info, Stack<T> Stack)
{
  return Cons(item, info, Stack);
}

lemma void RewritePushCons<T>(void* item, T info, Stack<T> Stack)
  requires emp;
  ensures Push(item, info, Stack) == Cons(item, info, Stack);
{
}

fixpoint Stack<T> Pop<T>(Stack<T> Stack)
{
  switch ( Stack )
  {
    case Nil:
      return Nil;

    case Cons(x, y, T):
      return T;
  }
}

fixpoint bool IsEmpty<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return true;
    
    case Cons(x, y, T):
      return false;
  }
}

lemma void IsEmptyNil<T>(Stack<T> S)
  requires emp;
  ensures IsEmpty(S) ? S == Nil : emp;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

fixpoint int Size<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return 0;
    
    case Cons(x, y, T):
      return 1 + Size(T);
  }
}

lemma void SizeEmptyStack<T>(Stack<T> S)
  requires emp;
  ensures IsEmpty(S) ? Size(S) == 0 : true;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

lemma void SizePush<T>(void* data, T info, Stack<T> S)
  requires emp;
  ensures Size( Push(data, info, S) ) == Size(S) + 1;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}


fixpoint void* GetTopPointer<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return 0;

    case Cons(x, y, z):
      return x;
  }  
}

lemma void PushNotNil<T>(void* data, T info, Stack<T> Stack)
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

struct stack* create_empty_stack/*@ <T> @*/(destructor* destructor)
  //@ requires [_]is_destructor<T>(destructor, ?Ownership);
  //@ ensures Stack(result, destructor, Ownership, ?Stack) &*& IsEmpty(Stack) == true;
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close StackItems(Ownership, 0, Nil);
  //@ close Stack(stack, destructor, Ownership, Nil);
  
  return stack;
}

void destroy_stack/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, _, _, ?S);
  //@ ensures emp;
{
  //@ open Stack(stack, _, _, S);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant [_]is_destructor<T>(destructor, ?Ownership) &*& StackItems(Ownership, current, _);
  {
    //@ open StackItems(_, _, _);
    //@ open Node(_, current, _, _, _);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  
  //@ open StackItems(_, current, _);
  free(stack);
}

void push/*@ <T> @*/(struct stack* stack, void* data)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack) &*& Ownership(data, ?info);
  //@ ensures Stack(stack, destructor, Ownership, Push(data, info, Stack));
{
  //@ open Stack(stack, destructor, Ownership, Stack);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  //@ close Node(Ownership, node, data, info, stack->first);
  //@ RewritePushCons(data, info, Stack);
  //@ close StackItems(Ownership, node, Push(data, info, Stack));
  
  stack->first = node;
  stack->size++;
  //@ close Stack(stack, destructor, Ownership, Push(data, info, Stack));
}

void* pop/*@ <T> @*/(struct stack* stack)
  /*@
  requires Stack<T>(stack, ?destructor, ?Ownership, Cons(?head, ?info, ?tail));
  @*/
  /*@
  ensures Stack(stack, destructor, Ownership, tail) &*&
          Ownership(head, info) &*& result == head;
  @*/
{
  //@ open Stack(stack, destructor, Ownership, ?Stack);
  struct node* first = stack->first;
  //@ open StackItems(_, first, _);
  //@ open Node(_, first, _, _, _);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  stack->size--;
  //@ close Stack(stack, destructor, Ownership, tail);
  
  return data;
}

destructor* get_destructor/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  /*@
  ensures Stack(stack, destructor, Ownership, Stack) &*&
          [_]is_destructor(result, Ownership) &*&
          result == destructor;
  @*/
{
  //@ open Stack(stack, destructor, Ownership, Stack);
  destructor* d = stack->destructor;
  //@ close Stack(stack, destructor, Ownership, Stack);
  return d;
}

void pop_destroy/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack) &*& Stack != Nil;
  //@ ensures Stack(stack, destructor, Ownership, Pop(Stack));
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}

bool is_empty/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Stack) &*& result == IsEmpty(Stack);
{
  //@ open Stack(stack, destructor, Ownership, Stack);
  struct node* first = stack->first;
  //@ open StackItems(Ownership, first, Stack);
  //@ close StackItems(Ownership, first, Stack);
  //@ close Stack(stack, destructor, Ownership, Stack);
  return first == 0;
}

int size/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Stack) &*& result == Size(Stack);
{
  //@ open Stack(stack, destructor, Ownership, Stack);
  int size = stack->size;
  //@ close Stack(stack, destructor, Ownership, Stack);
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
  //@ ensures Data(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close Data(data, foo, bar);
  return data;
}

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

predicate Data_Ownership(struct data *data, DataCarrier DC) = Data(data, GetFoo(DC), GetBar(DC));

@*/

void destroy_data(struct data* data)
  //@ requires Data_Ownership(data, _);
  //@ ensures emp;
{
  //@ open Data_Ownership(data, _);
  //@ open Data(data, _, _);
  free(data);
}

void check()
  //@ requires emp;
  //@ ensures emp;
{
  //@ produce_function_pointer_chunk destructor<DataCarrier>(destroy_data)(Data_Ownership)(data) { call(); }
  struct stack* stack = create_empty_stack(destroy_data);
  //@ assert Stack(stack, _, _, ?S0);
  //@ SizeEmptyStack(S0);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  //@ close Data_Ownership(data, DataCarrier(1, 2));
  push(stack, data);
  
  s = size(stack);
  //@ assert Stack(stack, _, _, ?S1);
  //@ SizePush(data, DataCarrier(1, 2), S0);
  //@ assert s == 1;
  
  data = create_data(2, 3);
  //@ close Data_Ownership(data, DataCarrier(2, 3));
  push(stack, data);

  s = size(stack);
  //@ assert Stack(stack, _, _, ?S2);
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
  //@ produce_function_pointer_chunk destructor<DataCarrier>(destroy_data)(Data_Ownership)(data) { call(); }
  struct stack* stack = create_empty_stack(destroy_data);
  //@ assert Stack(stack, _, _, ?InitStack);
  struct data* d1 = create_data(1, 1);
  //@ close Data_Ownership(d1, DataCarrier(1, 1));
  struct data* d2 = create_data(2, 2);
  //@ close Data_Ownership(d2, DataCarrier(2, 2));
  
  push(stack, d1);
  //@ assert Stack(stack, _, _, ?S);
  push(stack, d2);
  
  //@ PushNotNil(d2, DataCarrier(2, 2), S);
  struct data* d = pop(stack);
  //@ RewritePushCons(d2, DataCarrier(2, 2), S);
  //@ open Data_Ownership(d, ?DC);
  //@ open Data(d, ?foo, ?bar);
  //@ assert foo == 2;
  //@ assert bar == 2;
  //@ close Data(d, foo, bar);
  //@ close Data_Ownership(d, DC);
  destroy_data(d);
  
  //@ IsEmptyNil(InitStack);
  //@ PushNotNil(d1, DataCarrier(1, 1), Nil);
  d = pop(stack);
  //@ open Data_Ownership(d, ?DC2);
  //@ open Data(d, ?foo2, ?bar2);
  //@ assert foo2 == 1;
  //@ assert bar2 == 1;
  //@ close Data(d, foo2, bar2);
  //@ close Data_Ownership(d, DC2);
  
  destroy_data(d);
  
  destroy_stack(stack);
}

/*@

lemma void CheckPushPop<T>(void* item, T info, Stack<T> S)
  requires emp;
  ensures Pop( Push( item, info, S ) ) == S;
{
}

lemma void CheckSizePush<T>(void* item, T info, Stack<T> S)
  requires emp;
  ensures Size( Push( item, info, S ) ) == 1 + Size( S );
{
}

@*/