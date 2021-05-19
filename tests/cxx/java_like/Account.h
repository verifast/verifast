#pragma once

/*@
predicate AccountPred(Account *acc, int balance) =
    new_block_Account(acc) &*& acc->balance |-> balance;
@*/

class Account {
    int balance = 0;

public:
    int getBalance() const;
    //@ requires AccountPred(this, ?b);
    //@ ensures AccountPred(this, b) &*& result == b;
    
    void deposit(int amount);
    //@ requires AccountPred(this, ?b);
    //@ ensures AccountPred(this, b + amount);
    
    void transferTo(Account *target, int amount);
    //@ requires AccountPred(this, ?b) &*& AccountPred(target, ?t);
    //@ ensures AccountPred(this, b-amount) &*& AccountPred(target, t+amount);
};