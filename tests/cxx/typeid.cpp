struct S;
union U;

int main()
//@ requires true;
//@ ensures true;
{
    //@ std::type_info *t = &typeid(unsigned long);
    //@ t = &typeid(intptr_t);
    //@ t = &typeid(struct S);
    //@ t = &typeid(union U);
    //@ t = &typeid(bool);
    //@ t = &typeid(float);
    //@ t = &typeid(double);
    //@ t = &typeid(long double);
}