#include "Account.h"

int main()
//@ requires true;
//@ ensures true;
{
    Account *a = new Account;
    a->deposit(1000);
    
    Account *b = new Account;
    b->deposit(2000);
    
    a->transferTo(b, 500);
    
    int ba = a->getBalance();
    int bb = b->getBalance();
    //@ assert (ba == 500 && bb == 2500);
    
    //@ leak AccountPred(a, _);
    //@ leak AccountPred(b, _);
    //@ leak new_block_Account(a);
    //@ leak new_block_Account(b);
}