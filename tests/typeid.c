struct S;
union U;

int main()
//@ requires true;
//@ ensures true;
{
    //@ void *t = typeid(unsigned long);
    //@ t = typeid(intptr_t);
    //@ t = typeid(struct S);
    //@ t = typeid(union U);
    //@ t = typeid(bool);
    //@ t = typeid(float);
    //@ t = typeid(double);
    //@ t = typeid(long double);
    return 0;
}
