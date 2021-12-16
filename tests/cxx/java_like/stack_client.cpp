#include "Stack.h"

int main()
//@ requires true;
//@ ensures true;
{
    Stack *s = new Stack;
    s->push(10);
    s->push(20);
    s->pop();
    s->pop();
    //@ leak StackPred(s, _);
    //@ leak new_block_Stack(s);
}