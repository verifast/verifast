#include "Stack.h"

int Stack::Node::getSum() const
//@ requires nodes(?v, ?n, ?count, ?sum);
//@ ensures nodes(v, n, count, sum) &*& result == sum;
{
    //@ open nodes(v, n, count, sum);
    int result = value;
    if (next != 0) {
        int next_sum = next->getSum();
        result += next_sum;
    }
    return result;
    //@ close nodes(v, n, count, sum);
}

bool Stack::isEmpty() const
//@ requires valid(?count, ?sum);
//@ ensures valid(count, sum) &*& result == (count == 0);
{
    //@ open this->valid(count, sum);
    return hd == 0;
    //@ close valid(count, sum);
}

int Stack::peek() const
//@ requires valid(?count, ?sum) &*& count > 0;
//@ ensures valid(count, sum);
{
    //@ open valid(count, sum);
    //@ open this->hd->nodes(?val, ?next, count, sum);
    return hd->value;
    //@ close this->hd->nodes(val, next, count, sum);
    //@ close valid(count, sum);
}

int Stack::getSum() const
//@ requires valid(?count, ?sum);
//@ ensures valid(count, sum) &*& result == sum;
{
    int result;
    //@ open valid(count, sum);
    if (hd != 0) {
        result = hd->getSum();
    } else {
        result = 0;
    }
    //@ close valid(count, sum);
    return result;
}

void Stack::push(int value)
//@ requires valid(?count, ?sum);
//@ ensures valid(count + 1, sum + value);
{
    //@ open valid(count, sum);
    Node *n = new Node(value);
    //@ open n->nodes(value, _, 1, value);
    n->next = hd;
    hd = n;
    //@ close n->nodes(value, _, count + 1, sum + value);
    //@ close valid(count + 1, sum + value);
}

int Stack::pop()
//@ requires valid(?count, ?sum) &*& count > 0;
//@ ensures valid(count - 1, ?nsum) &*& result == sum - nsum; 
{
    //@ open valid(count, sum);
    struct Stack::Node *hd = this->hd;
    //@ open hd->nodes(_, _, count, sum);
    int result = hd->value;
    this->hd = hd->next;
    hd->next = 0;
    //@ close hd->nodes(_, 0, 1, _);
    delete hd;
    //@ close valid(count - 1, sum - result);
    return result;
}