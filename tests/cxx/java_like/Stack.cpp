#include "Stack.h"

int Stack::Node::getSum() const
//@ requires nodes(this, ?count);
//@ ensures nodes(this, count);
{
    int result = 0;
    //@ open nodes(this, count);
    if (next != 0) {
        result = next->getSum();
        result += value;
    }
    //@ close nodes(this, count);
    return result;
}

bool Stack::isEmpty() const
//@ requires StackPred(this, ?count);
//@ ensures StackPred(this, count) &*& result == (count == 0);
{
    //@ open StackPred(this, count);
    //@ open nodes(this->head, count);
    return head == 0;
    //@ close nodes(this->head, count);
    //@ close StackPred(this, count);
}

int Stack::peek() const
//@ requires StackPred(this, ?count) &*& count > 0;
//@ ensures StackPred(this, count);
{
    //@ open StackPred(this, count);
    //@ open nodes(this->head, count);
    return head->value;
    //@ close nodes(this->head, count);
    //@ close StackPred(this, count);
}

int Stack::getSum() const
//@ requires StackPred(this, ?count);
//@ ensures StackPred(this, count);
{
    int result = 0;
    //@ open StackPred(this, count);
    if (head != 0)
        result = head->getSum();
    else
       result = 0;
    //@ close StackPred(this, count);
    return result;
}

void Stack::push(int value)
//@ requires StackPred(this, ?count);
//@ ensures StackPred(this, count + 1);
{
    //@ open StackPred(this, count);
    Node *n = new Node;
    n->next = head;
    n->value = value;
    head = n;
    //@ close nodes(n, count + 1);
    //@ close StackPred(this, count + 1);
}

int main()
//@ requires true;
//@ ensures true;
{
    Stack *s = new Stack;
    //@ close nodes(s->head, 0);
    //@ close StackPred(s, 0);
    s->push(10);
    s->push(20);
    //@ leak StackPred(s, 2);   
}