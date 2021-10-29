#include "Stack.h"

int Stack::Node::getSum() const
//@ requires this != 0 &*& nodes(this, ?count);
//@ ensures this != 0 &*&nodes(this, count);
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

int Stack::pop()
//@ requires StackPred(this, ?count) &*& 0 < count;
//@ ensures StackPred(this, count - 1);
{
    //@ open StackPred(this, count);
    struct Stack::Node *head = this->head;
    //@ open nodes(head, count);
    int result = head->value;
    this->head = head->next;
    delete head;
    //@ close StackPred(this, count - 1);
    return result;
}