#include "Account.h"

int Account::getBalance() const
//@ requires AccountPred(this, ?b);
//@ ensures AccountPred(this, b) &*& result == b;
{
    //@ open AccountPred(this, b);
    return balance;
    //@ close AccountPred(this, b);
}
    
void Account::deposit(int amount)
//@ requires AccountPred(this, ?b);
//@ ensures AccountPred(this, b + amount);
{
    //@ open AccountPred(this, b);
    balance += amount;
    //@ close AccountPred(this, b + amount);
}
    
void Account::transferTo(Account *target, int amount)
//@ requires AccountPred(this, ?b) &*& AccountPred(target, ?t);
//@ ensures AccountPred(this, b-amount) &*& AccountPred(target, t+amount);
{
    deposit(-amount);
    target->deposit(amount);
}