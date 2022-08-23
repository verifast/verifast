typedef int (*myFuncDef)(int, int);
//@ requires true;
//@ ensures true;

int addInt(int n, int m) //@ : myFuncDef
//@ requires true;
//@ ensures true;
{
	    return n+m;
}


int test(int n) 
//@ requires true;
//@ ensures true;
{
    myFuncDef functionPtr = &addInt;
    int sum = (*functionPtr)(2, 3);
    return sum;
}
