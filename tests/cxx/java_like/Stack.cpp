#include "Stack.h"

int Stack::Node::getSum() const
//@ requires nodes(this, ?count, ?sum);
//@ ensures nodes(this, count, sum) &*& result == sum;
{
    //@ open nodes(this, count, sum);
    int result = value;
    if (next != 0) {
        int next_sum = next->getSum();
        result += next_sum;
    }
    //@ open nodes(this->next, count - 1, sum - this->value);
    //@ close nodes(this->next, count - 1, sum - this->value);
    //@ close nodes(this, count, sum);
    return result;
}

bool Stack::isEmpty() const
//@ requires StackPred(this, ?count, ?sum);
//@ ensures StackPred(this, count, sum) &*& result == (count == 0);
{
    //@ open StackPred(this, count, sum);
    //@ open nodes(this->head, count, sum);
    return head == 0;
    //@ close nodes(this->head, count, sum);
    //@ close StackPred(this, count, sum);
}

int Stack::peek() const
//@ requires StackPred(this, ?count, ?sum) &*& count > 0;
//@ ensures StackPred(this, count, sum);
{
    //@ open StackPred(this, count, sum);
    //@ open nodes(this->head, count, sum);
    return head->value;
    //@ close nodes(this->head, count, sum);
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
    //@ open nodes(this->head, count, sum);
    //@ close nodes(this->head, count, sum);
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
    //@ close nodes(n, count + 1, sum + value);
    //@ close StackPred(this, count + 1, sum + value);
}

int Stack::pop()
//@ requires StackPred(this, ?count, ?sum) &*& count > 0;
//@ ensures StackPred(this, count - 1, ?nsum) &*& result == sum - nsum; 
{
    //@ open StackPred(this, count, sum);
    struct Stack::Node *head = this->head;
    //@ open nodes(head, count, sum);
    int result = head->value;
    this->head = head->next;
    delete head;
    //@ close StackPred(this, count - 1, sum - result);
    return result;
}