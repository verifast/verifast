#include "stdlib.h"

struct account {
    int balance;
};

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account myAccountLocal;
    struct account *myAccount = &myAccountLocal;
    myAccount->balance = 5;
    //free(myAccount);
    return 0;
}