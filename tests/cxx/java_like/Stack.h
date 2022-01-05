#pragma once

/*@
predicate nodes(Stack::Node *node, int count, int sum) =
    node == 0 ?
        count == 0 && sum == 0
    :
        count > 0 &*& new_block_Stack::Node(node) &*&
        node->value |-> ?value &*& node->next |-> ?next &*&
        nodes(next, ?ncount, ?nsum) &*& count == ncount + 1 &*& sum == nsum + value;
@*/

/*@
predicate StackPred(Stack *stack, int count, int sum) =
    stack->head |-> ?head &*&
    count >= 0 &*& nodes(head, count, sum);
@*/

class Stack {

    struct Node {
        int value;
        Node *next;
        
        Node(int value) : value(value), next(nullptr)
        //@ requires true;
        //@ ensures this->value |-> value &*& this->next |-> 0;
        {}

        int getSum() const;
        //@ requires nodes(this, ?count, ?sum);
        //@ ensures nodes(this, count, sum) &*& result == sum;
    };

    Node *head;

    public:
    Stack() : head(nullptr)
    //@ requires true;
    //@ ensures StackPred(this, 0, 0);
    {
    	//@ close nodes(this->head, 0, 0);
    	//@ close StackPred(this, 0, 0);
    }
    
    void push(int value);
    //@ requires StackPred(this, ?count, ?sum);
    //@ ensures StackPred(this, count + 1, sum + value);

    int peek() const;
    //@ requires StackPred(this, ?count, ?sum) &*& count > 0;
    //@ ensures StackPred(this, count, sum);

    bool isEmpty() const;
    //@ requires StackPred(this, ?count, ?sum);
    //@ ensures StackPred(this, count, sum) &*& result == (count == 0);

    int pop();
    //@ requires StackPred(this, ?count, ?sum) &*& count > 0;
    //@ ensures StackPred(this, count - 1, ?nsum) &*& result == sum - nsum; 
    
    int getSum() const;
    //@ requires StackPred(this, ?count, ?sum);
    //@ ensures StackPred(this, count, sum) &*& result == sum;
};