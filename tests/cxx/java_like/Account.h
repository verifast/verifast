#pragma once

/*@
predicate AccountPred(Account *acc, int balance;) =
    new_block_Account(acc) &*& acc->balance |-> balance;
    
lemma void AccountNotNull(Account* acc);
    requires AccountPred(acc, ?balance);
    ensures AccountPred(acc, balance) &*& acc != 0;

lemma_auto void AccountPred_inv();
    requires AccountPred(?account, ?balance);
    ensures AccountPred(account, balance) &*& account != 0;
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