struct S;
union U;

int main()
//@ requires true;
//@ ensures true;
{
    //@ void *t = typeid(unsigned long);
    //@ assert sizeof((pointer)t) == sizeof(unsigned long);
    //@ t = typeid(intptr_t);
    //@ assert sizeof((pointer)t) == sizeof(intptr_t);
    //@ t = typeid(struct S);
    //@ assert sizeof((pointer)t) == sizeof(struct S);
    //@ t = typeid(union U);
    //@ t = typeid(bool);
    //@ assert sizeof((pointer)t) == sizeof(bool);
    //@ t = typeid(float);
    //@ assert sizeof((pointer)t) == sizeof(float);
    //@ t = typeid(double);
    //@ assert sizeof((pointer)t) == sizeof(double);
    //@ t = typeid(long double);
    return 0;
}
