#include "Stack.h"

int Stack::Node::getSum() const
//@ requires nodes(this, ?v, ?n, ?count, ?sum);
//@ ensures nodes(this, v, n, count, sum) &*& result == sum;
{
    int result = value;
    if (next != 0) {
        int next_sum = next->getSum();
        result += next_sum;
    }
    return result;
}

bool Stack::isEmpty() const
//@ requires StackPred(this, ?count, ?sum);
//@ ensures StackPred(this, count, sum) &*& result == (count == 0);
{
    //@ open StackPred(this, count, sum);
    return head == 0;
    //@ close StackPred(this, count, sum);
}

int Stack::peek() const
//@ requires StackPred(this, ?count, ?sum) &*& count > 0;
//@ ensures StackPred(this, count, sum);
{
    //@ open StackPred(this, count, sum);
    return head->value;
    //@ close StackPred(this, count, sum);
}

int Stack::getSum() const
//@ requires StackPred(this, ?count, ?sum);
//@ ensures StackPred(this, count, sum) &*& result == sum;
{
    int result;
    //@ open StackPred(this, count, sum);
    if (head != 0) {
        result = head->getSum();
    } else {
        result = 0;
    }
    //@ close StackPred(this, count, sum);
    return result;
}

void Stack::push(int value)
//@ requires StackPred(this, ?count, ?sum);
//@ ensures StackPred(this, count + 1, sum + value);
{
    //@ open StackPred(this, count, sum);
    Node *n = new Node(value);
    n->next = head;
    head = n;
    //@ close StackPred(this, count + 1, sum + value);
}

int Stack::pop()
//@ requires StackPred(this, ?count, ?sum) &*& count > 0;
//@ ensures StackPred(this, count - 1, ?nsum) &*& result == sum - nsum; 
{
    //@ open StackPred(this, count, sum);
    struct Stack::Node *head = this->head;
    int result = head->value;
    this->head = head->next;
    head->next = 0;
    delete head;
    //@ close StackPred(this, count - 1, sum - result);
    return result;
}