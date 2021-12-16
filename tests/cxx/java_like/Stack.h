#pragma once

/*@
predicate nodes(Stack::Node *node, int count) =
    node == 0 ?
        count == 0
    :
        count > 0 &*& new_block_Stack::Node(node) &*&
        node->value |-> _ &*& node->next |-> ?next &*&
        nodes(next, ?ncount) &*& count == ncount + 1;
@*/

/*@
predicate StackPred(Stack *stack, int count) =
    stack->head |-> ?head &*&
    count >= 0 &*& nodes(head, count);
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
        //@ requires nodes(this, ?count);
        //@ ensures nodes(this, count);
    };

    Node *head;

    public:
    Stack() : head(nullptr)
    //@ requires true;
    //@ ensures StackPred(this, 0);
    {
    	//@ close nodes(this->head, 0);
    	//@ close StackPred(this, 0);
    }
    
    void push(int value);
    //@ requires StackPred(this, ?count);
    //@ ensures StackPred(this, count + 1);

    int peek() const;
    //@ requires StackPred(this, ?count) &*& count > 0;
    //@ ensures StackPred(this, count);

    bool isEmpty() const;
    //@ requires StackPred(this, ?count);
    //@ ensures StackPred(this, count) &*& result == (count == 0);

    int pop();
    //@ requires StackPred(this, ?count) &*& count > 0;
    //@ ensures StackPred(this, count - 1);
    
    int getSum() const;
    //@ requires StackPred(this, ?count);
    //@ ensures StackPred(this, count);
};