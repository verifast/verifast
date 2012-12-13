#include "stdio.h"

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    char msg[10] = "Hi there!";
    
    printf("Hello, world!\n");
    printf("Hello, %s!\n", "world!");
    printf("%s\n", msg);
    printf("%d divided by %d is %d with remainder %d.\n", 10, 3, 10 / 3, 10 % 3);
    return 0;
}