#pragma once

/*@
predicate AccountPred(Account *account, int balance) =
    account != 0 &*& account->balance |-> balance;
    
lemma_auto void AccountPred_inv()
    requires [?f]AccountPred(?account, ?balance);
    ensures [f]AccountPred(account, balance) &*& account != 0;
{
    open [f]AccountPred(account, balance);
    close [f]AccountPred(account, balance);
}
@*/

class Account {
    int balance;

public:
    Account() : balance(0)
    //@ requires true;
    //@ ensures AccountPred(this, 0);
    {
    	//@ close AccountPred(this, 0);
    }

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