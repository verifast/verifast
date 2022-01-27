#include "Account.h"

int main()
//@ requires true;
//@ ensures true;
{
    Account a;
    Account b;
    
    a.deposit(1000);
    b.deposit(2000);
    a.transferTo(&b, 500);
    
    int ba = a.getBalance();
    int bb = b.getBalance();
    //@ assert (ba == 500 && bb == 2500);
}