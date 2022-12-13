#pragma once

class Stack {

    struct Node {
        int value;
        Node *next;

        /*@
        predicate nodes(int value, Stack::Node *next, int count, int sum) =
            this->value |-> value &*& 
            this->next |-> next &*&
            (
                next == 0
                    ? count == 1 &*& sum == value
                    : new_block_Stack::Node(next) &*& 
                    next->nodes(&typeid(struct Stack::Node))(_, _, ?ncount, ?nsum) &*& 
                    count == ncount + 1 &*& 
                    count > 1 &*&
                    sum == nsum + value
            );
        @*/
        
        Node(int value) : value(value), next(nullptr)
        //@ requires true;
        //@ ensures nodes(value, 0, 1, value);
        {
            //@ close nodes(value, 0, 1, value);
        }

        ~Node()
        //@ requires nodes(_, _, _, _);
        //@ ensures true;
        {
            //@ open nodes(_, _, _, _);
            if (next) {
                delete next;
            }
        }

        int getSum() const;
        //@ requires nodes(?v, ?n, ?count, ?sum);
        //@ ensures nodes(v, n, count, sum) &*& result == sum;
    };

    Node *hd;

    public:
    /*@
    predicate valid(int count, int sum) =
        this != 0 &*&
        this->hd |-> ?hd &*&
        (
            hd == 0
                ? count == 0 &*& sum == 0
                : new_block_Stack::Node(hd) &*& hd->nodes(&typeid(struct Stack::Node))(_, _, count, sum) &*& count > 0
        );
    @*/

    Stack() : hd(nullptr)
    //@ requires true;
    //@ ensures valid(0, 0);
    {
    	//@ close valid(0, 0);
    }

    ~Stack()
    //@ requires valid(_, _);
    //@ ensures true;
    {
        //@ open valid(_, _);
        if (hd) {
            delete hd;
        }
    }
    
    void push(int value);
    //@ requires valid(?count, ?sum);
    //@ ensures valid(count + 1, sum + value);

    int peek() const;
    //@ requires valid(?count, ?sum) &*& count > 0;
    //@ ensures valid(count, sum);

    bool isEmpty() const;
    //@ requires valid(?count, ?sum);
    //@ ensures valid(count, sum) &*& result == (count == 0);

    int pop();
    //@ requires valid(?count, ?sum) &*& count > 0;
    //@ ensures valid(count - 1, ?nsum) &*& result == sum - nsum; 
    
    int getSum() const;
    //@ requires valid(?count, ?sum);
    //@ ensures valid(count, sum) &*& result == sum;
};