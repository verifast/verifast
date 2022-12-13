#include "Account.h"

int Account::getBalance() const
//@ requires valid(?b);
//@ ensures valid(b) &*& result == b;
{
    //@ open valid(b);
    return balance;
    //@ close valid(b);
}
    
void Account::deposit(int amount)
//@ requires valid(?b);
//@ ensures valid(b + amount);
{
    //@ open valid(b);
    balance += amount;
    //@ close valid(b + amount);
}
    
void Account::transferTo(Account *target, int amount)
//@ requires this->valid(&typeid(struct Account))(?b) &*& target->valid(&typeid(struct Account))(?t);
//@ ensures this->valid(&typeid(struct Account))(b-amount) &*& target->valid(&typeid(struct Account))(t+amount);
{
    deposit(-amount);
    target->deposit(amount);
}