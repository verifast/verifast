#pragma once

class Account {
    int balance;

public:
    /*@
    predicate valid(int balance) =
        this != 0 &*& this->balance |-> balance;
    @*/

    Account() : balance(0)
    //@ requires true;
    //@ ensures valid(0);
    {
    	//@ close valid(0);
    }
    
    ~Account()
    //@ requires valid(_);
    //@ ensures true;
    {
        //@ open valid(_);
    }

    int getBalance() const;
    //@ requires valid(?b);
    //@ ensures valid(b) &*& result == b;
    
    void deposit(int amount);
    //@ requires valid(?b);
    //@ ensures valid(b + amount);
    
    void transferTo(Account *target, int amount);
    //@ requires this->valid(&typeid(struct Account))(?b) &*& target->valid(&typeid(struct Account))(?t);
    //@ ensures this->valid(&typeid(struct Account))(b-amount) &*& target->valid(&typeid(struct Account))(t+amount);
};