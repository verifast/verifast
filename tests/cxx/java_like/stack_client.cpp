#include "Stack.h"

int main()
//@ requires true;
//@ ensures true;
{
    Stack *s = new Stack;
    //@ close nodes(s->head, 0);
    //@ close StackPred(s, 0);
    s->push(10);
    s->push(20);
    s->pop();
    s->pop();
    //@ open StackPred(s, _);
    //@ open nodes(s->head, _);
    delete s;
}