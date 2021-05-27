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

int main()
//@ requires true;
//@ ensures true;
{
    Account *a = new Account;
    //@ close AccountPred(a, 0);
    a->deposit(1000);
    
    Account *b = new Account;
    //@ close AccountPred(b, 0);
    b->deposit(2000);
    
    a->transferTo(b, 500);
    
    int ba = a->getBalance();
    int bb = b->getBalance();
    //@ assert (ba == 500 && bb == 2500);
    //@ leak AccountPred(a, _);
    //@ leak AccountPred(b, _);
}