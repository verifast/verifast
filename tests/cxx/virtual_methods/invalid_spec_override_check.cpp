struct A {
    virtual ~A()
    //@ requires thisType != &typeid(B);
    //@ ensures true;
    {}
};

struct B : public A {
    ~B()
    //@ requires false;
    //@ ensures true;
    {}
};

struct C : public B {
    ~C()
    //@ requires false; //~ override check with ~A fails
    //@ ensures true;
    {}
};