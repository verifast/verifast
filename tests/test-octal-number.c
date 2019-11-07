#include <stdio.h>
int main()
//@ requires true;
//@ ensures true;
{
	if (0666 == 666){
	  //@ assert(false); // Cannot happen, 0666 is octal.
	}
	
	//@ assert 0666 != 666;
	//@ assert 0666 == 438;
	//@ assert 01 == 1;
	//@ assert 001 == 1;
	//@ assert 010 == 8;
	//@ assert 012345670 == 2739128;

        return 0;
}
