#include "Account.h"

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
    
    delete a;
    delete b;
}