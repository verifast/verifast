#pragma once

/*@
predicate nodes(Stack::Node *node; int value, Stack::Node *next, int count, int sum) =
    node->value |-> value &*& 
    node->next |-> next &*&
    (
        next == 0
            ? count == 1 &*& sum == value
            : new_block_Stack::Node(next) &*& 
              nodes(next, _, _, ?ncount, ?nsum) &*& 
              count == ncount + 1 &*& 
              count > 1 &*&
              sum == nsum + value
    );
@*/

/*@
predicate StackPred(Stack *stack, int count, int sum) =
    stack->head |-> ?head &*&
    (
        head == 0
            ? count == 0 &*& sum == 0
            : new_block_Stack::Node(head) &*& nodes(head, _, _, count, sum) &*& count > 0
    );
@*/

class Stack {

    struct Node {
        int value;
        Node *next;
        
        Node(int value) : value(value), next(nullptr)
        //@ requires true;
        //@ ensures nodes(this, value, 0, 1, value);
        {
        }

        ~Node()
        //@ requires nodes(this, _, _, _, _);
        //@ ensures true;
        {
            if (next) {
                delete next;
            }
        }

        int getSum() const;
        //@ requires nodes(this, ?v, ?n, ?count, ?sum);
        //@ ensures nodes(this, v, n, count, sum) &*& result == sum;
    };

    Node *head;

    public:
    Stack() : head(nullptr)
    //@ requires true;
    //@ ensures StackPred(this, 0, 0);
    {
    	//@ close StackPred(this, 0, 0);
    }

    ~Stack()
    //@ requires StackPred(this, _, _);
    //@ ensures true;
    {
        //@ open StackPred(this, _, _);
        if (head) {
            delete head;
        }
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