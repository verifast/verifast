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
    new_block_Stack(stack) &*& stack->head |-> ?head &*& 
    count >= 0 &*& nodes(head, count);
@*/

class Stack {

    struct Node {
        int value;
        Node *next = nullptr;

        int getSum() const;
        //@ requires this != 0 &*& nodes(this, ?count);
        //@ ensures this != 0 &*& nodes(this, count);
    };

    Node *head = nullptr;

    public:
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